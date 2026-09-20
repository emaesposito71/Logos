#!/usr/bin/env python3
"""
sport.py — scarica i loghi delle squadre americane (NBA, NFL, NHL, MLB, WNBA,
UFL, NCAA) in WebP leggeri, pronti per l'uso runtime in un'app Android.

Sorgente: API pubblica ESPN (site.api.espn.com) + CDN loghi (a.espncdn.com).
  Per ogni lega scarica l'elenco squadre (50 per pagina, paginato), poi
  scarica il logo PNG 500px di ogni squadra e lo riduce/ricodifica in WebP.
  Sono 2 tipi di richiesta e niente di più: l'API è aperta e funziona bene
  anche da GitHub Actions (i download passano da curl perché Akamai
  blocca l'impronta TLS di Python, ma per il resto è tutto standard).

NOTA su SportsLogos.net: è il sito di riferimento per questi loghi, ma è
dietro Cloudflare (challenge JavaScript): blocca script, curl e le stesse
GitHub Actions. L'API di ESPN copre gli stessi sport principali in modo
stabile e scaricabile; la qualità (PNG 500px) è identica a quella mostrata
da ESPN su telefono e TV.

Leghe disponibili (chiave -> lega ESPN):

    nfl       NFL (football americano)            ~32 squadre
    nba       NBA (basket)                        ~30 squadre
    wnba      WNBA (basket femminile)             ~15 squadre
    nhl       NHL (hockey ghiaccio)               ~32 squadre
    mlb       MLB (baseball)                      ~30 squadre
    ufl       UFL (football prof., spring league) ~8 squadre
    ncaa-mb   NCAA basket maschile (Div. I)       ~362 squadre
    ncaa-wb   NCAA basket femminile (Div. I)      ~362 squadre
    ncaa-fb   NCAA football (tutte le divisioni)  ~762 squadre
    ncaa-base NCAA baseball (Div. I)              ~437 squadre
    ncaa-hm   NCAA hockey maschile (Div. I)       ~116 squadre
    ncaa-hw   NCAA hockey femminile (Div. I)      ~47 squadre
    ncaa-vb   NCAA pallavolo femminile (Div. I)   ~359 squadre

Non disponibile da ESPN (testato direttamente sull'API):
  - F1: ESPN non espone i loghi dei team via API.
  - Leghe minori USA: MiLB (baseball), AHL/ECHL (hockey), NBA G League
    (basket) NON esistono come endpoint dell'API ESPN (404); TheSportsDB
    con chiave gratuita ora espone solo 5 leghe; i siti ufficiali (MiLB.com,
    theahl.com, nba.com) sono dietro WAF Akamai che blocca anche curl.
    Nota: nelle leghe NCAA ci sono ~150 squadre di Divisione 2/3 che su
    ESPN NON hanno proprio un logo: vengono contate a parte ("senza logo"),
    non come errori.

Struttura prodotta:

    sport/
    ├── index.json                  # manifesto: metadati + hash di ogni logo
    ├── index.min.json              # indice compatto pensato per l'app
    ├── nfl/
    │   ├── arizona_cardinals.webp
    │   └── ...
    ├── nba/
    └── ncaa-mb/
        └── ...

Uso runtime nell'app (la repo fa da CDN):
    https://raw.githubusercontent.com/emaesposito71/Logos/main/sport/nba/boston_celtics.webp
    Indice completo: .../main/sport/index.min.json

Esecuzioni incrementali: le squadre già scaricate e invariate vengono
saltate (confronto dell'URL del logo registrato nel manifesto), quindi le
run successive scaricano solo le novità. L'URL del logo è stabile nel
tempo: per forzare il riscaricamento usa --force.

Rispetto anti-sovraccarico: pochi worker, pausa tra le richieste, backoff
con rispetto di Retry-After, pausa globale condivisa sui 429 e stop
automatico se il rate limit diventa persistente (codice di uscita 3).

Esempi:
    python3 scripts/sport.py                            # tutte le leghe
    python3 scripts/sport.py --leagues nba,nfl          # solo alcune leghe
    python3 scripts/sport.py --leagues nba --limit 5    # prova veloce
    python3 scripts/sport.py --size 256                 # loghi più piccoli
    python3 scripts/sport.py --force                    # riscarica tutto

Fonte dati: ESPN (i marchi restano dei rispettivi proprietari; uso
personale/editoriale, non commerciale).
"""

from __future__ import annotations

import argparse
import json
import os
import random
import re
import sys
import threading
import time
import urllib.parse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

API_BASE = "https://site.api.espn.com/apis/site/v2/sports"
PAGE_SIZE = 50  # l'API ESPN restituisce 50 squadre per pagina

# L'API e il CDN di ESPN sono dietro Akamai: le richieste "finte browser"
# (UA Chrome con impronta TLS non-browser) vengono bloccate con 403.
# Il modo affidabile: curl PURO, senza header extra — l'UA di default
# "curl/x.y" è coerente con l'impronta TLS e Akamai lo accetta (il CDN
# immagini invece accetta qualunque UA). Da GitHub Actions curl è
# preinstallato: nessuna dipendenza aggiuntiva.
JSON_HEADERS: dict[str, str] = {}
IMG_HEADERS: dict[str, str] = {}

# Chiave -> (percorso API ESPN, nome lega per il manifesto)
LEAGUES: dict[str, tuple[str, str]] = {
    "nfl":       ("football/nfl", "NFL"),
    "nba":       ("basketball/nba", "NBA"),
    "wnba":      ("basketball/wnba", "WNBA"),
    "nhl":       ("hockey/nhl", "NHL"),
    "mlb":       ("baseball/mlb", "MLB"),
    "ncaa-mb":   ("basketball/mens-college-basketball", "NCAA basket maschile"),
    "ncaa-wb":   ("basketball/womens-college-basketball", "NCAA basket femminile"),
    "ncaa-fb":   ("football/college-football", "NCAA football"),
    "ufl":       ("football/ufl", "UFL"),
    "ncaa-base": ("baseball/college-baseball", "NCAA baseball"),
    "ncaa-hm":   ("hockey/mens-college-hockey", "NCAA hockey maschile"),
    "ncaa-hw":   ("hockey/womens-college-hockey", "NCAA hockey femminile"),
    "ncaa-vb":   ("volleyball/womens-college-volleyball", "NCAA pallavolo femminile"),
}

PNG_MAGIC = b"\x89PNG\r\n\x1a\n"


class RateLimitExceeded(Exception):
    """L'API/CDN risponde 429 in modo persistente: meglio fermarsi e riprovare dopo."""


# Pausa globale condivisa tra i thread dopo un HTTP 429: quando il server
# ci rallenta, TUTTI i worker si fermano per non peggiorare la situazione.
_rate_lock = threading.Lock()
_rate_cooldown_until = 0.0
_consec_429 = 0
MAX_CONSEC_429 = 20
_abort = threading.Event()


def log(msg: str) -> None:
    print(msg, flush=True)


def sanitize(name: str) -> str:
    """'Boston Celtics' -> 'boston_celtics' (file sicuri per ogni OS)."""
    return re.sub(r"[^a-z0-9._-]+", "_", name.lower()).strip("_") or "squadra"


def _set_cooldown(seconds: float) -> None:
    global _rate_cooldown_until
    with _rate_lock:
        _rate_cooldown_until = max(_rate_cooldown_until, time.monotonic() + seconds)


def polite_wait(cfg: dict) -> None:
    """Pausa educata prima di ogni richiesta + rispetto del cooldown globale."""
    delay = cfg.get("delay", 0) or 0
    if delay > 0:
        time.sleep(delay + random.uniform(0, delay * 0.5))
    while True:
        if _abort.is_set():
            raise RateLimitExceeded("run interrotta per rate limit persistente")
        with _rate_lock:
            remaining = _rate_cooldown_until - time.monotonic()
        if remaining <= 0:
            return
        time.sleep(min(remaining, 2.0))


def fetch_bytes(url: str, headers: dict, timeout: int, retries: int,
                cfg: dict | None = None) -> bytes:
    """Scarica un URL in memoria con retry + backoff. Solleva l'ultima eccezione.

    Passa da curl: l'API/CDN di ESPN è dietro Akamai, che blocca
    l'impronta TLS di Python (urllib/requests -> HTTP 403) mentre curl
    passa sempre. curl è preinstallato sia qui che sui runner GitHub.

    I 429 (rate limit) hanno attese più lunghe, rispettano Retry-After e
    attivano una pausa globale per tutti i thread. Dopo troppi 429
    consecutivi solleva RateLimitExceeded per fermare la run.
    """
    global _consec_429
    last_err: Exception | None = None
    host = urllib.parse.urlparse(url).netloc
    cur_headers = dict(headers)
    for attempt in range(retries):
        if _abort.is_set():
            raise RateLimitExceeded("run interrotta per rate limit persistente")
        if cfg:
            polite_wait(cfg)
        try:
            code, data, retry_after = _curl(url, cur_headers, timeout)
            if code == 403 and cur_headers:
                # Akamai a volte rifiuta gli header personalizzati: ritenta
                # subito in modalità curl puro (senza header).
                log(f"  ... HTTP 403 con header personalizzati da {host}: "
                    f"ritento senza header")
                cur_headers = {}
                code, data, retry_after = _curl(url, cur_headers, timeout)
            if code == 200:
                with _rate_lock:
                    _consec_429 = 0
                return data
            if code == 429:
                wait = max(5 * (2 ** attempt), retry_after)
                with _rate_lock:
                    _consec_429 += 1
                    trips = _consec_429 >= MAX_CONSEC_429
                _set_cooldown(20)
                log(f"  ... HTTP 429 da {host} (tentativo {attempt + 1}/{retries}), "
                    f"attendo {wait}s")
                if trips:
                    _abort.set()
                    raise RateLimitExceeded(
                        f"rate limit persistente su {host}: "
                        f"{MAX_CONSEC_429} risposte 429 consecutive")
            else:
                wait = 2 ** attempt
                last_err = RuntimeError(f"HTTP {code} da {url}")
            if attempt < retries - 1:
                time.sleep(wait)
        except RateLimitExceeded:
            raise
        except Exception as e:  # curl fallito, timeout, DNS, reset...
            last_err = e
            if attempt < retries - 1:
                time.sleep(2 ** attempt)
    assert last_err is not None
    raise last_err


def _curl(url: str, headers: dict, timeout: int) -> tuple[int, bytes, int]:
    """Chiama curl e ritorna (status_http, corpo, retry_after). Solleva su errore di rete."""
    import subprocess
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        body = os.path.join(td, "body")
        hdrs = os.path.join(td, "headers")
        cmd = ["curl", "-sS", "--compressed", "--max-time", str(timeout),
               "-o", body, "-D", hdrs, "-w", "%{http_code}"]
        for k, v in headers.items():
            cmd += ["-H", f"{k}: {v}"]
        cmd.append(url)
        p = subprocess.run(cmd, capture_output=True, text=True)
        if p.returncode != 0:
            raise RuntimeError(f"curl fallito: {(p.stderr or '').strip()[:200]}")
        try:
            code = int((p.stdout or "").strip() or 0)
        except ValueError:
            code = 0
        retry_after = 0
        if os.path.exists(hdrs):
            with open(hdrs, encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    if line.lower().startswith("retry-after:"):
                        try:
                            retry_after = int(line.split(":", 1)[1].strip())
                        except (TypeError, ValueError):
                            retry_after = 0
        data = b""
        if os.path.exists(body):
            with open(body, "rb") as fh:
                data = fh.read()
        return code, data, retry_after


def is_valid_png(data: bytes) -> bool:
    return len(data) > 100 and data[:8] == PNG_MAGIC


def is_valid_webp(data: bytes) -> bool:
    return len(data) > 50 and data[:4] == b"RIFF" and data[8:12] == b"WEBP"


def png_to_webp(data: bytes, max_px: int, quality: int) -> bytes:
    """Riduce un PNG a max_px di lato massimo e lo ricodifica in WebP con alpha."""
    import io

    from PIL import Image
    im = Image.open(io.BytesIO(data))
    if im.mode != "RGBA":
        im = im.convert("RGBA")
    im.thumbnail((max_px, max_px), Image.LANCZOS)
    buf = io.BytesIO()
    # method=4: encoding ~3x più veloce di method=6 con file ~5% più grandi
    im.save(buf, "WEBP", quality=quality, method=4)
    return buf.getvalue()


def save_file(data: bytes, path: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".part"
    with open(tmp, "wb") as f:
        f.write(data)
    os.replace(tmp, path)


def fetch_league(key: str, path: str, cfg: dict) -> list[dict]:
    """Scarica l'elenco completo delle squadre di una lega (paginato)."""
    teams: list[dict] = []
    page = 1
    while True:
        url = f"{API_BASE}/{path}/teams?page={page}"
        raw = fetch_bytes(url, JSON_HEADERS, cfg["timeout"], cfg["retries"], cfg=cfg)
        try:
            d = json.loads(raw)
        except ValueError as e:
            raise RuntimeError(f"risposta JSON non valida da {url}: {e}")
        sports = d.get("sports") or [{}]
        leagues = sports[0].get("leagues") or [{}]
        batch = leagues[0].get("teams") or []
        if not batch:
            break
        for t in batch:
            tm = t.get("team") or {}
            logos = tm.get("logos") or []
            href = (logos[0].get("href", "") if logos else "").strip()
            teams.append({
                "id": str(tm.get("id", "")),
                "name": (tm.get("displayName") or tm.get("name") or "").strip(),
                "abbr": (tm.get("abbreviation") or "").strip(),
                "logo": href,
            })
        if len(batch) < PAGE_SIZE:
            break
        page += 1
        if page > 40:  # rete di sicurezza: nessuna lega è così grande
            break
    return teams


def build_entries(teams: list[dict], league_key: str, league_name: str) -> list[dict]:
    """Da squadre API a 'entries': una per logo, con slug univoco nella lega."""
    used: set[str] = set()
    entries: list[dict] = []
    for t in teams:
        base = sanitize(t["name"] or t["abbr"] or f"squadra-{t['id']}")
        slug, n = base, 2
        while slug in used:  # nomi uguali nella stessa lega: aggiungi -2, -3...
            slug = f"{base}-{n}"
            n += 1
        used.add(slug)
        entries.append({
            "league": league_key,
            "league_name": league_name,
            "id": t["id"],
            "name": t["name"] or slug,
            "slug": slug,
            "logo_url": t["logo"],
        })
    return entries


def process_team(entry: dict, cfg: dict, manifest_logos: dict) -> dict:
    """Scarica il logo di una squadra e lo salva come WebP. Ritorna l'esito."""
    league = entry["league"]
    slug = entry["slug"]
    key = f"{league}/{slug}"
    out = cfg["out"]
    max_px = cfg["size"]
    quality = cfg["quality"]

    if not entry["logo_url"]:
        # Squadra senza logo su ESPN (es. college football Divisione 2/3):
        # non è un errore. Registriamo lo stato e nelle run successive la
        # saltiamo, così non viene ritentata all'infinito.
        prev = manifest_logos.get(key) if not cfg["force"] else None
        if prev and prev.get("logo_missing"):
            return {"key": key, "status": "skipped"}
        return {
            "key": key, "status": "missing", "errors": [],
            "manifest": {
                "name": entry["name"],
                "league": league,
                "league_name": entry["league_name"],
                "slug": slug,
                "team_id": entry["id"],
                "logo_url": "",
                "logo_missing": True,
                "hash": "missing",
                "webp": max_px,
                "webp_quality": quality,
                "webp_file": None,
                "fetched_at": datetime.now(timezone.utc).isoformat(),
            },
        }

    # Skip incrementale: stesso URL logo + stesso WebP + file esistente.
    prev = manifest_logos.get(key) if not cfg["force"] else None
    if prev and prev.get("logo_url") != entry["logo_url"]:
        prev = None
    if prev and prev.get("webp") == max_px and prev.get("webp_file"):
        rec = prev["webp_file"]
        if rec.get("hash") == entry["logo_url"] \
                and os.path.exists(os.path.join(out, rec["file"])):
            return {"key": key, "status": "skipped"}

    dest_rel = os.path.join(league, f"{slug}.webp")
    errors: list[str] = []
    webp_file: dict | None = None
    try:
        data = fetch_bytes(entry["logo_url"], IMG_HEADERS, cfg["timeout"],
                           cfg["retries"], cfg=cfg)
        if not is_valid_png(data):
            raise ValueError("contenuto non-PNG")
        webp = png_to_webp(data, max_px, quality)
        if not is_valid_webp(webp):
            raise ValueError("conversione WebP fallita")
        save_file(webp, os.path.join(out, dest_rel))
        webp_file = {"hash": entry["logo_url"], "file": dest_rel}
    except RateLimitExceeded:
        raise
    except Exception as e:
        errors.append(f"webp: {e}")

    status = "ok" if not errors else "failed"
    return {
        "key": key,
        "status": status,
        "errors": errors,
        "manifest": {
            "name": entry["name"],
            "league": league,
            "league_name": entry["league_name"],
            "slug": slug,
            "team_id": entry["id"],
            "logo_url": entry["logo_url"],
            "hash": entry["logo_url"],   # rilevatore di modifiche (URL stabile)
            "webp": max_px,
            "webp_quality": quality,
            "webp_file": webp_file,
            "fetched_at": datetime.now(timezone.utc).isoformat(),
        },
    }


def write_manifest(out_dir: str, logos: dict, cfg: dict) -> None:
    """Scrive il manifesto in modo atomico (usato anche per i salvataggi parziali).

    Nel manifesto le squadre restano TUTTE (anche quelle senza logo, con
    logo_missing=true, così le run successive le saltano), ma "count"
    conta solo i loghi realmente presenti.
    """
    real = sum(1 for m in logos.values() if m.get("webp_file"))
    manifest = {
        "source": "ESPN (site.api.espn.com + a.espncdn.com)",
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "webp": cfg["size"],
        "webp_quality": cfg["quality"],
        "count": real,
        "teams": len(logos),
        "missing": len(logos) - real,
        "logos": dict(sorted(logos.items())),
    }
    path = os.path.join(out_dir, "index.json")
    save_file(json.dumps(manifest, ensure_ascii=False, indent=1).encode("utf-8"), path)


def write_compact_index(out_dir: str, logos: dict) -> None:
    """Indice compatto (index.min.json) pensato per le app: una voce per logo
    con nome, lega e file, senza i metadati di scaricamento. Le squadre
    senza logo NON compaiono: l'app vede solo file esistenti."""
    real = {k: m for k, m in logos.items() if m.get("webp_file")}
    compact = {
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "count": len(real),
        "logos": {
            key: {
                "name": m.get("name", ""),
                "league": m.get("league", ""),
                "slug": m.get("slug", ""),
                "file": (m.get("webp_file") or {}).get("file", ""),
            }
            for key, m in sorted(real.items())
        },
    }
    path = os.path.join(out_dir, "index.min.json")
    save_file(json.dumps(compact, ensure_ascii=False,
                         separators=(",", ":")).encode("utf-8"), path)


def write_github_summary(path: str, stats: dict, failures: list[dict],
                         leagues: dict) -> None:
    lines = [
        "## 🏈 Sincronizzazione loghi sport (ESPN)",
        "",
        f"- Loghi elaborati: **{stats['total']}**",
        f"- Scaricati/aggiornati: **{stats['ok']}** ({stats['files']} file)",
        f"- Saltati (già aggiornati): **{stats['skipped']}**",
        f"- Falliti: **{stats['failed']}**",
        f"- Senza logo su ESPN: **{stats.get('missing', 0)}** "
        "(squadre senza immagine disponibile, es. college football Div. 2/3)",
        "",
        "<details><summary>Loghi per lega</summary>",
        "",
        "| Lega | Loghi |",
        "|---|---|",
    ]
    for c, n in sorted(leagues.items(), key=lambda x: -x[1]):
        lines.append(f"| {c} | {n} |")
    lines.append("</details>")
    if failures:
        lines += ["", "### ❌ Errori (primi 20)", ""]
        for f in failures[:20]:
            lines.append(f"- `{f['key']}`: {'; '.join(f['errors'])}")
        lines += ["",
                  "> ℹ️ Rilancia il workflow per completare i loghi falliti: "
                  "i file già scaricati vengono riusati, si scarica solo ciò che manca."]
    lines.append("")
    with open(path, "a", encoding="utf-8") as fh:
        fh.write("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Scarica i loghi NFL/NBA/WNBA/NHL/MLB/UFL e NCAA (basket, "
                    "football, baseball, hockey, pallavolo) da ESPN, in WebP leggeri.")
    ap.add_argument("--out", default="sport",
                    help="Cartella di destinazione (default: sport)")
    ap.add_argument("--leagues", default="",
                    help="Solo queste leghe, separate da virgola "
                         f"(valori: {','.join(LEAGUES)}). Default: tutte.")
    ap.add_argument("--size", type=int, default=512,
                    help="Lato massimo in px del WebP (default: 512; "
                         "cambiare il valore riscarica tutto)")
    ap.add_argument("--quality", type=int, default=80,
                    help="Qualità WebP da 1 a 100 (default: 80)")
    ap.add_argument("--limit", type=int, default=0,
                    help="Scarica al massimo N loghi in totale (0 = tutti)")
    ap.add_argument("--workers", type=int, default=4,
                    help="Download paralleli (default: 4; abbassa se vedi HTTP 429)")
    ap.add_argument("--delay", type=float, default=0.3,
                    help="Pausa in secondi prima di ogni richiesta (default: 0.3)")
    ap.add_argument("--force", action="store_true",
                    help="Riscarica tutto, anche se presente")
    ap.add_argument("--prune", action="store_true",
                    help="Rimuove dal manifesto/file le squadre sparite dall'API "
                         "(solo run complete)")
    ap.add_argument("--timeout", type=int, default=30,
                    help="Timeout HTTP in secondi (default: 30)")
    ap.add_argument("--retries", type=int, default=3,
                    help="Tentativi per download (default: 3)")
    args = ap.parse_args()

    if args.prune and args.limit:
        log("ERRORE: --prune si può usare solo su run complete (senza --limit).")
        return 1

    wanted = {c.strip().lower() for c in args.leagues.split(",") if c.strip()}
    unknown = wanted - set(LEAGUES)
    if unknown:
        log(f"ERRORE: leghe non riconosciute: {', '.join(sorted(unknown))}. "
            f"Valori validi: {', '.join(LEAGUES)}")
        return 1

    try:
        import PIL  # noqa: F401
    except ImportError:
        log("ERRORE: questo script richiede Pillow (pip install pillow).")
        return 1

    # --- elenco squadre per ogni lega richiesta ------------------------------
    cfg = {"out": args.out, "size": max(16, args.size),
           "quality": max(1, min(100, args.quality)), "force": args.force,
           "timeout": args.timeout, "retries": args.retries,
           "delay": max(0.0, args.delay)}

    entries: list[dict] = []
    league_counts: dict[str, int] = {}
    for key in LEAGUES:
        if wanted and key not in wanted:
            continue
        path, name = LEAGUES[key]
        log(f"Lega {name}: scarico l'elenco squadre...")
        try:
            teams = fetch_league(key, path, cfg)
        except RateLimitExceeded:
            log(f"ERRORE fatale: rate limit persistente mentre leggo {name}.")
            return 3
        except Exception as e:
            log(f"ATTENZIONE: impossibile leggere la lega {name}: {e}")
            continue
        built = build_entries(teams, key, name)
        entries.extend(built)
        league_counts[key] = len(built)
        log(f"Lega {name}: {len(built)} squadre.")

    if not entries:
        log("ERRORE: nessuna squadra trovata (controlla la connessione).")
        return 1

    entries.sort(key=lambda e: (e["league"], e["slug"]))
    if args.limit and args.limit > 0:
        entries = entries[: args.limit]
        log(f"Limite attivo: elaboro {len(entries)} loghi.")

    manifest_path = os.path.join(args.out, "index.json")
    manifest_logos: dict = {}
    if os.path.exists(manifest_path):
        try:
            with open(manifest_path, encoding="utf-8") as f:
                manifest_logos = json.load(f).get("logos", {})
            log(f"Manifesto esistente: {len(manifest_logos)} voci.")
        except Exception as e:
            log(f"ATTENZIONE: manifesto illeggibile ({e}), riparto da zero.")

    log(f"Modalità WebP leggera: output {args.out}/<lega>/<slug>.webp a "
        f"{cfg['size']}px (qualità {cfg['quality']}). "
        f"2 richieste per squadra max (pagina API + logo).")

    stats = {"total": len(entries), "ok": 0, "skipped": 0,
             "failed": 0, "files": 0, "missing": 0}
    failures: list[dict] = []
    lock = threading.Lock()
    done = 0
    t0 = time.time()

    workers = max(1, min(args.workers, 16))
    est_min = len(entries) * 1.0 * cfg["delay"] * 1.25 / workers / 60
    log(f"Avvio download: {len(entries)} loghi, {workers} worker, "
        f"pausa {cfg['delay']}s.")
    if len(entries) > 0:
        log(f"Stima indicativa: ~{max(1, est_min):.0f} minuti "
            f"(dipende dalla velocità di risposta).")

    FLUSH_EVERY = 50  # salva il manifesto ogni N loghi scaricati: se la run
    next_flush = FLUSH_EVERY  # viene interrotta, i progressi restano salvati

    aborted: Exception | None = None
    pool = ThreadPoolExecutor(max_workers=workers)
    try:
        futs = {pool.submit(process_team, e, cfg, manifest_logos): e for e in entries}
        for fut in as_completed(futs):
            try:
                res = fut.result()
            except RateLimitExceeded as e:
                aborted = e
                _abort.set()
                for f in futs:
                    f.cancel()
                break
            need_flush = False
            with lock:
                done += 1
                st = res["status"]
                stats[st] = stats.get(st, 0) + 1
                if st in ("ok", "missing"):
                    m = res["manifest"]
                    manifest_logos[res["key"]] = m
                    if st == "ok":
                        stats["files"] += 1 if m.get("webp_file") else 0
                        if stats["ok"] >= next_flush:
                            need_flush = True
                            next_flush += FLUSH_EVERY
                if st == "failed":
                    failures.append(res)
                if done % 50 == 0 or done == len(entries):
                    el = time.time() - t0
                    log(f"... {done}/{len(entries)} ({el:.0f}s) "
                        f"ok={stats['ok']} skip={stats['skipped']} "
                        f"fail={stats['failed']} no_logo={stats['missing']}")
            if need_flush:
                # Salvataggio parziale atomico: anche se la run viene cancellata
                # o il processo ucciso, i loghi già completati non si ripescano.
                write_manifest(args.out, manifest_logos, cfg)
    finally:
        pool.shutdown(wait=False, cancel_futures=True)

    if aborted is not None:
        log("")
        log(f"INTERROTTO: {aborted}")
        log("Il server sta limitando le richieste in modo persistente. I progressi")
        log("parziali sono salvati nel manifesto: rilancia più tardi (eventualmente")
        log("con --delay più alto o --workers più basso) per completare i mancanti.")

    # --- prune (solo run complete non interrotte) ------------------------------
    pruned = 0
    if args.prune and aborted is None:
        live = {f"{e['league']}/{e['slug']}" for e in entries}
        for key in list(manifest_logos.keys()):
            if key not in live:
                m = manifest_logos.pop(key)
                if m.get("webp_file"):
                    p = os.path.join(args.out, m["webp_file"]["file"])
                    if os.path.exists(p):
                        os.remove(p)
                        pruned += 1
        log(f"Prune: rimosse {pruned} squadre non più presenti nell'API.")

    # --- manifesto + indice compatto ------------------------------------------
    os.makedirs(args.out, exist_ok=True)
    write_manifest(args.out, manifest_logos, cfg)
    write_compact_index(args.out, manifest_logos)

    el = time.time() - t0
    log("")
    log(f"FINITO in {el:.0f}s: ok={stats['ok']} saltati={stats['skipped']} "
        f"falliti={stats['failed']} senza_logo={stats['missing']} "
        f"file_scaricati={stats['files']}")
    if stats["missing"]:
        log(f"Nota: {stats['missing']} squadre non hanno un logo su ESPN "
            f"(es. college football Divisione 2/3): non sono errori e non "
            f"verranno ritentate.")
    if failures:
        log("Primi errori:")
        for f in failures[:10]:
            log(f"  - {f['key']}: {'; '.join(f['errors'])}")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        per_league: dict[str, int] = {}
        for m in manifest_logos.values():
            if not m.get("webp_file"):
                continue  # nell'indice per lega solo i loghi realmente presenti
            ln = m.get("league_name") or m.get("league", "?")
            per_league[ln] = per_league.get(ln, 0) + 1
        try:
            write_github_summary(summary_path, stats, failures, per_league)
        except Exception as e:
            log(f"(impossibile scrivere il riepilogo GitHub: {e})")
    return 3 if aborted is not None else 0


if __name__ == "__main__":
    sys.exit(main())
