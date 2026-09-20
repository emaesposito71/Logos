#!/usr/bin/env python3
"""
tennis.py — scarica i ritratti a mezzobusto dei tennisti ATP/WTA da ESPN,
in WebP leggeri pronti per l'uso runtime in un'app Android (telefono/TV).

Fonte: classifiche ufficiali ESPN (site.api.espn.com, API pubblica) + CDN
immagini (a.espncdn.com). Ogni giro scarica il TOP 150 ATP e il TOP 150 WTA
(= i giocatori attivi con pagina profilo su espn.com/tennis/players), poi
scarica il ritratto PNG (tip. 600x436, mezzobusto) e lo riduce/ricodifica
in WebP mantenendo le proporzioni.

Perché le classifiche? L'elenco "players" del sito ESPN non ha un'API
dedicata (la pagina HTML è dietro Akamai: blocca anche curl), mentre le
classifiche ATP/WTA sono esattamente la lista dei giocatori attivi di
spicco e vengono con nome, rank e punti. L'archivio completo dell'API
(18.000+ atleti) è quasi tutto giocatori storici/inattivi SENZA ritratto:
inutile iterarlo.

Ritratti: ESPN NON ha la foto per tutti. Nel payload delle classifiche il
campo "headshot" è popolato solo per ~1/3 dei giocatori, ma circa metà
degli altri ha comunque l'immagine sul CDN con lo schema standard
  https://a.espncdn.com/i/headshots/tennis/players/full/<id>.png
quindi per OGNI giocatore si prova il download diretto: se il PNG esiste
si salva, altrimenti il giocatore viene registrato come "senza ritratto"
(nel manifesto, con headshot assente) e nelle run successive viene saltato.
Usa --retry-missing per riprovare i senza-ritratto (ESPN aggiunge foto nel
tempo) oppure --force per riscaricare tutto.

Struttura prodotta (TUTTI i ritratti in un'unica cartella, il nome del
giocatore è nel nome del file):

    sports/tennis/
    ├── index.json                # manifesto: metadati + stato di ogni giocatore
    ├── index.min.json            # indice compatto pensato per l'app
    ├── jannik_sinner.webp
    ├── coco_gauff.webp
    └── ...

Nella stessa cartella convivono anche i vecchi PNG (es. JSINNER.png)
migrati dalla precedente cartella tennis/ della root: l'indice elenca
solo i WebP prodotti da questo script.

Uso runtime nell'app (la repo fa da CDN):
    https://raw.githubusercontent.com/emaesposito71/Logos/main/sports/tennis/jannik_sinner.webp
    Indice completo: .../main/sports/tennis/index.min.json

Incrementale: i giocatori già scaricati (stesso URL ritratto, stessa
dimensione WebP, file esistente) vengono saltati; "rank" e "punti" però
vengono sempre aggiornati nel manifesto perché cambiano ogni settimana.

Rispetto anti-sovraccarico: pochi worker, pausa tra le richieste, backoff
con rispetto di Retry-After, pausa globale condivisa sui 429 e stop
automatico se il rate limit diventa persistente (codice di uscita 3).

Esempi:
    python3 scripts/tennis.py                      # ATP + WTA complete
    python3 scripts/tennis.py --tours atp --limit 20   # prova veloce
    python3 scripts/tennis.py --retry-missing      # riprova i senza-ritratto
"""

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

API_BASE = "https://site.api.espn.com/apis/site/v2/sports/tennis"
CDN_HEADSHOT = "https://a.espncdn.com/i/headshots/tennis/players/full/{id}.png"

# Tornei (chiave -> (percorso API, nome per il manifesto)). Solo singolare:
# le classifiche doppio di ESPN non sono esposte con atleti embedded.
TOURS: dict[str, tuple[str, str]] = {
    "atp": ("atp", "ATP"),
    "wta": ("wta", "WTA"),
}

# Le richieste passano da curl in modalità pura (senza header): l'impronta
# TLS di curl è coerente con l'UA "curl/x.y" e Akamai la accetta (testato:
# UA browser via curl -> 403; Python urllib/requests -> 403).
JSON_HEADERS: dict[str, str] = {}
IMG_HEADERS: dict[str, str] = {}

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
    """'Jannik Sinner' -> 'jannik_sinner' (file sicuri per ogni OS)."""
    return re.sub(r"[^a-z0-9._-]+", "_", name.lower()).strip("_") or "giocatore"


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


class NotFound(Exception):
    """HTTP 404 definitivo (il ritratto non esiste): inutile ritentare."""


def fetch_bytes(url: str, headers: dict, timeout: int, retries: int,
                cfg: dict | None = None) -> bytes:
    """Scarica un URL in memoria con retry + backoff.

    Passa da curl: API e CDN ESPN sono dietro Akamai, che blocca
    l'impronta TLS di Python (urllib/requests -> HTTP 403) mentre curl
    passa. I 404 sollevano NotFound subito (nessun ritentativo: il file
    non c'è e ritentare è solo spreco). I 429 (rate limit) hanno attese
    più lunghe, rispettano Retry-After e attivano una pausa globale per
    tutti i thread; dopo troppi 429 consecutivi solleva
    RateLimitExceeded per fermare la run.
    """
    global _consec_429
    last_err: Exception | None = None
    host = urllib.parse.urlparse(url).netloc
    for attempt in range(retries):
        if _abort.is_set():
            raise RateLimitExceeded("run interrotta per rate limit persistente")
        if cfg:
            polite_wait(cfg)
        try:
            code, data, retry_after = _curl(url, headers, timeout)
            if code == 200:
                with _rate_lock:
                    _consec_429 = 0
                return data
            if code == 404:
                raise NotFound(f"HTTP 404 (inesistente) da {url}")
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
        except (RateLimitExceeded, NotFound):
            raise
        except Exception as e:  # curl fallito, timeout, DNS, reset...
            last_err = e
            if attempt < retries - 1:
                time.sleep(2 ** attempt)
    assert last_err is not None
    raise last_err


def is_valid_png(data: bytes) -> bool:
    return len(data) > 100 and data[:8] == PNG_MAGIC


def is_valid_webp(data: bytes) -> bool:
    return len(data) > 50 and data[:4] == b"RIFF" and data[8:12] == b"WEBP"


def png_to_webp(data: bytes, max_px: int, quality: int) -> bytes:
    """Riduce un PNG a max_px di lato massimo (mantenendo le proporzioni)
    e lo ricodifica in WebP con alpha. I ritratti ESPN sono 600x436:
    il risultato resta orizzontale (mezzobusto)."""
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


def headshot_href(athlete: dict) -> str:
    """URL del ritratto: dal payload se c'è, altrimenti lo schema standard
    del CDN (che spesso esiste anche quando il campo è omesso)."""
    hs = athlete.get("headshot")
    if isinstance(hs, dict):
        href = (hs.get("href") or "").strip()
        if href.startswith("http"):
            return href
    if isinstance(hs, str) and hs.startswith("http"):
        return hs
    aid = str(athlete.get("id", "")).strip()
    if aid:
        return CDN_HEADSHOT.format(id=aid)
    return ""


def fetch_tour(tour_key: str, cfg: dict) -> list[dict]:
    """Scarica la classifica di un tour e restituisce una voce per giocatore."""
    path, name = TOURS[tour_key]
    url = f"{API_BASE}/{path}/rankings"
    raw = fetch_bytes(url, JSON_HEADERS, cfg["timeout"], cfg["retries"], cfg=cfg)
    try:
        d = json.loads(raw)
    except ValueError as e:
        raise RuntimeError(f"risposta JSON non valida da {url}: {e}")
    ranks = ((d.get("rankings") or [{}])[0]).get("ranks") or []
    players: list[dict] = []
    for it in ranks:
        ath = it.get("athlete") or {}
        nm = (ath.get("displayName") or
              " ".join(x for x in (ath.get("firstName"), ath.get("lastName")) if x)).strip()
        if not nm:
            continue
        players.append({
            "id": str(ath.get("id", "")).strip(),
            "name": nm,
            "rank": it.get("current"),
            "points": it.get("points"),
            "headshot_url": headshot_href(ath),
        })
    if not players:
        raise RuntimeError(f"classifica {name} vuota o inattesa da {url}")
    return players


def build_entries(players: list[dict], tour_key: str, tour_name: str,
                  used: set[str]) -> list[dict]:
    """Da giocatori API a 'entries': una per giocatore, slug univoco su
    tutta la cartella di output (i file sono flat: ATP e WTA insieme)."""
    entries: list[dict] = []
    for p in players:
        base = sanitize(p["name"])
        slug, n = base, 2
        while slug in used:  # nomi uguali (anche tra ATP e WTA): aggiungi -2, -3...
            slug = f"{base}-{n}"
            n += 1
        used.add(slug)
        entries.append({
            "tour": tour_key,
            "tour_name": tour_name,
            "id": p["id"],
            "name": p["name"],
            "slug": slug,
            "rank": p["rank"],
            "points": p["points"],
            "headshot_url": p["headshot_url"],
        })
    return entries


def process_player(entry: dict, cfg: dict, manifest_logos: dict) -> dict:
    """Scarica il ritratto di un giocatore e lo salva come WebP. Ritorna l'esito."""
    tour = entry["tour"]
    slug = entry["slug"]
    key = f"{tour}/{slug}"
    out = cfg["out"]
    max_px = cfg["size"]
    quality = cfg["quality"]

    prev = manifest_logos.get(key) if not cfg["force"] else None

    # Giocatore già provato SENZA ritratto: si salta (ESPN aggiunge foto nel
    # tempo: usa --retry-missing per riprovarli). Si riprova solo se l'API
    # ora propone un URL candidato diverso da quello già provato e fallito
    # (tried_url); i record più vecchi senza tried_url si saltano sempre.
    tried = entry["headshot_url"]
    if prev and prev.get("logo_missing") and not cfg["retry_missing"]:
        if "tried_url" not in prev or prev.get("tried_url") == tried:
            return {"key": key, "status": "skipped"}

    if not tried:
        return {
            "key": key, "status": "missing", "errors": [],
            "manifest": {
                "name": entry["name"],
                "tour": tour,
                "tour_name": entry["tour_name"],
                "slug": slug,
                "player_id": entry["id"],
                "rank": entry["rank"],
                "points": entry["points"],
                "headshot_url": "",
                "tried_url": "",
                "logo_missing": True,
                "hash": "missing",
                "webp": max_px,
                "webp_quality": quality,
                "webp_file": None,
                "fetched_at": datetime.now(timezone.utc).isoformat(),
            },
        }

    # Skip incrementale: stesso URL ritratto + stesso WebP + file esistente.
    # rank/punti vengono comunque aggiornati nel manifesto alla fine della run.
    if prev and prev.get("headshot_url") != entry["headshot_url"]:
        prev = None
    if prev and prev.get("webp") == max_px and prev.get("webp_file"):
        rec = prev["webp_file"]
        if rec.get("hash") == entry["headshot_url"] \
                and os.path.exists(os.path.join(out, rec["file"])):
            return {"key": key, "status": "skipped",
                    "manifest": {**prev, "rank": entry["rank"],
                                 "points": entry["points"]}}

    dest_rel = f"{slug}.webp"
    errors: list[str] = []
    webp_file: dict | None = None
    try:
        data = fetch_bytes(entry["headshot_url"], IMG_HEADERS, cfg["timeout"],
                           cfg["retries"], cfg=cfg)
        if not is_valid_png(data):
            raise ValueError("contenuto non-PNG")
        webp = png_to_webp(data, max_px, quality)
        if not is_valid_webp(webp):
            raise ValueError("conversione WebP fallita")
        save_file(webp, os.path.join(out, dest_rel))
        webp_file = {"hash": entry["headshot_url"], "file": dest_rel}
    except NotFound:
        # Ritratto davvero assente su ESPN: lo registriamo come "senza
        # ritratto" (con l'URL provato) così le run successive lo saltano
        # (--retry-missing per riprovarli, o quando l'URL cambia).
        return {
            "key": key, "status": "missing", "errors": [],
            "manifest": {
                "name": entry["name"],
                "tour": tour,
                "tour_name": entry["tour_name"],
                "slug": slug,
                "player_id": entry["id"],
                "rank": entry["rank"],
                "points": entry["points"],
                "headshot_url": "",
                "tried_url": entry["headshot_url"],
                "logo_missing": True,
                "hash": "missing",
                "webp": max_px,
                "webp_quality": quality,
                "webp_file": None,
                "fetched_at": datetime.now(timezone.utc).isoformat(),
            },
        }
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
            "tour": tour,
            "tour_name": entry["tour_name"],
            "slug": slug,
            "player_id": entry["id"],
            "rank": entry["rank"],
            "points": entry["points"],
            "headshot_url": entry["headshot_url"],
            "hash": entry["headshot_url"],  # rilevatore di modifiche (URL stabile)
            "webp": max_px,
            "webp_quality": quality,
            "webp_file": webp_file,
            "fetched_at": datetime.now(timezone.utc).isoformat(),
        },
    }


def write_manifest(out_dir: str, logos: dict, cfg: dict) -> None:
    """Scrive il manifesto in modo atomico (usato anche per i salvataggi parziali).

    Nel manifesto i giocatori restano TUTTI (anche quelli senza ritratto, con
    logo_missing=true, così le run successive li saltano), ma "count" conta
    solo i ritratti realmente presenti.
    """
    real = sum(1 for m in logos.values() if m.get("webp_file"))
    manifest = {
        "source": "ESPN (site.api.espn.com + a.espncdn.com)",
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "webp": cfg["size"],
        "webp_quality": cfg["quality"],
        "count": real,
        "players": len(logos),
        "missing": len(logos) - real,
        "logos": dict(sorted(logos.items())),
    }
    path = os.path.join(out_dir, "index.json")
    save_file(json.dumps(manifest, ensure_ascii=False, indent=1).encode("utf-8"), path)


def write_compact_index(out_dir: str, logos: dict) -> None:
    """Indice compatto (index.min.json) pensato per le app: una voce per
    ritratto con nome, tour, rank e file. I giocatori senza ritratto NON
    compaiono: l'app vede solo file esistenti."""
    real = {k: m for k, m in logos.items() if m.get("webp_file")}
    compact = {
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "count": len(real),
        "logos": {
            key: {
                "name": m.get("name", ""),
                "tour": m.get("tour", ""),
                "slug": m.get("slug", ""),
                "rank": m.get("rank"),
                "file": (m.get("webp_file") or {}).get("file", ""),
            }
            for key, m in sorted(real.items())
        },
    }
    path = os.path.join(out_dir, "index.min.json")
    save_file(json.dumps(compact, ensure_ascii=False,
                         separators=(",", ":")).encode("utf-8"), path)


def write_github_summary(path: str, stats: dict, failures: list[dict],
                         tours: dict) -> None:
    lines = [
        "## 🎾 Sincronizzazione ritratti tennisti (ESPN)",
        "",
        f"- Giocatori elaborati: **{stats['total']}**",
        f"- Ritratti scaricati/aggiornati: **{stats['ok']}** ({stats['files']} file)",
        f"- Saltati (già aggiornati): **{stats['skipped']}**",
        f"- Falliti: **{stats['failed']}**",
        f"- Senza ritratto su ESPN: **{stats.get('missing', 0)}** "
        "(registrati nel manifesto; riprovali con --retry-missing)",
        "",
        "<details><summary>Ritratti per tour</summary>",
        "",
        "| Tour | Ritratti |",
        "|---|---|",
    ]
    for c, n in sorted(tours.items(), key=lambda x: -x[1]):
        lines.append(f"| {c} | {n} |")
    lines.append("</details>")
    if failures:
        lines += ["", "### ❌ Errori (primi 20)", ""]
        for f in failures[:20]:
            lines.append(f"- `{f['key']}`: {'; '.join(f['errors'])}")
        lines += ["",
                  "> ℹ️ Rilancia il workflow per completare i ritratti falliti: "
                  "i file già scaricati vengono riusati, si scarica solo ciò che manca."]
    lines.append("")
    with open(path, "a", encoding="utf-8") as fh:
        fh.write("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Scarica i ritratti dei tennisti ATP/WTA da ESPN, "
                    "in WebP leggeri.")
    ap.add_argument("--out", default="sports/tennis",
                    help="Cartella di destinazione (default: sports/tennis)")
    ap.add_argument("--tours", default="",
                    help="Solo questi tour, separati da virgola "
                         f"(valori: {','.join(TOURS)}). Default: tutti.")
    ap.add_argument("--size", type=int, default=512,
                    help="Lato massimo in px del WebP (default: 512; "
                         "cambiare il valore riscarica tutto)")
    ap.add_argument("--quality", type=int, default=80,
                    help="Qualità WebP da 1 a 100 (default: 80)")
    ap.add_argument("--limit", type=int, default=0,
                    help="Scarica al massimo N ritratti in totale (0 = tutti)")
    ap.add_argument("--workers", type=int, default=4,
                    help="Download paralleli (default: 4; abbassa se vedi HTTP 429)")
    ap.add_argument("--delay", type=float, default=0.2,
                    help="Pausa in secondi prima di ogni richiesta (default: 0.2)")
    ap.add_argument("--force", action="store_true",
                    help="Riscarica tutto, anche se presente")
    ap.add_argument("--retry-missing", action="store_true",
                    help="Riprova anche i giocatori registrati come senza ritratto")
    ap.add_argument("--prune", action="store_true",
                    help="Rimuove dal manifesto/file i giocatori usciti dalle "
                         "classifiche (solo run complete; di default lo storico "
                         "acquisito viene conservato)")
    ap.add_argument("--timeout", type=int, default=30,
                    help="Timeout HTTP in secondi (default: 30)")
    ap.add_argument("--retries", type=int, default=3,
                    help="Tentativi per download (default: 3)")
    args = ap.parse_args()

    if args.prune and args.limit:
        log("ERRORE: --prune si può usare solo su run complete (senza --limit).")
        return 1

    wanted = {c.strip().lower() for c in args.tours.split(",") if c.strip()}
    unknown = wanted - set(TOURS)
    if unknown:
        log(f"ERRORE: tour non riconosciuti: {', '.join(sorted(unknown))}. "
            f"Valori validi: {', '.join(TOURS)}")
        return 1

    try:
        import PIL  # noqa: F401
    except ImportError:
        log("ERRORE: questo script richiede Pillow (pip install pillow).")
        return 1

    cfg = {"out": args.out, "size": max(16, args.size),
           "quality": max(1, min(100, args.quality)), "force": args.force,
           "retry_missing": args.retry_missing,
           "timeout": args.timeout, "retries": args.retries,
           "delay": max(0.0, args.delay)}

    # --- classifica di ogni tour richiesto -----------------------------------
    entries: list[dict] = []
    tour_counts: dict[str, int] = {}
    used_slugs: set[str] = set()  # slug unici su tutta la cartella (file flat)
    for key in TOURS:
        if wanted and key not in wanted:
            continue
        path, name = TOURS[key]
        log(f"Tour {name}: scarico la classifica...")
        try:
            players = fetch_tour(key, cfg)
        except RateLimitExceeded:
            log(f"ERRORE fatale: rate limit persistente mentre leggo {name}.")
            return 3
        except Exception as e:
            log(f"ATTENZIONE: impossibile leggere il tour {name}: {e}")
            continue
        built = build_entries(players, key, name, used_slugs)
        entries.extend(built)
        tour_counts[key] = len(built)
        con_url = sum(1 for e in built if e["headshot_url"])
        log(f"Tour {name}: {len(built)} giocatori "
            f"(headshot nel payload: {con_url}, gli altri si prova il CDN).")

    if not entries:
        log("ERRORE: nessun giocatore trovato (controlla la connessione).")
        return 1

    entries.sort(key=lambda e: (e["tour"], e["slug"]))
    if args.limit and args.limit > 0:
        entries = entries[: args.limit]
        log(f"Limite attivo: elaboro {len(entries)} giocatori.")

    manifest_path = os.path.join(args.out, "index.json")
    manifest_logos: dict = {}
    if os.path.exists(manifest_path):
        try:
            with open(manifest_path, encoding="utf-8") as f:
                manifest_logos = json.load(f).get("logos", {})
            log(f"Manifesto esistente: {len(manifest_logos)} voci.")
        except Exception as e:
            log(f"ATTENZIONE: manifesto illeggibile ({e}), riparto da zero.")

    log(f"Modalità WebP leggera: output {args.out}/<slug>.webp a "
        f"{cfg['size']}px (qualità {cfg['quality']}). "
        f"1 classifica per tour + 1 richiesta per giocatore.")

    stats = {"total": len(entries), "ok": 0, "skipped": 0,
             "failed": 0, "files": 0, "missing": 0}
    failures: list[dict] = []
    lock = threading.Lock()
    done = 0
    t0 = time.time()

    workers = max(1, min(args.workers, 16))
    est_min = len(entries) * 1.0 * cfg["delay"] * 1.25 / workers / 60
    log(f"Avvio download: {len(entries)} giocatori, {workers} worker, "
        f"pausa {cfg['delay']}s.")
    if len(entries) > 0:
        log(f"Stima indicativa: ~{max(1, est_min):.0f} minuti "
            f"(dipende dalla velocità di risposta).")

    FLUSH_EVERY = 50  # salva il manifesto ogni N ritratti: se la run
    next_flush = FLUSH_EVERY  # viene interrotta, i progressi restano salvati

    aborted: Exception | None = None
    pool = ThreadPoolExecutor(max_workers=workers)
    try:
        futs = {pool.submit(process_player, e, cfg, manifest_logos): e for e in entries}
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
                if st in ("ok", "missing", "skipped"):
                    m = res.get("manifest")
                    if m is not None:
                        manifest_logos[res["key"]] = m
                    if st == "ok":
                        stats["files"] += 1 if res["manifest"].get("webp_file") else 0
                        if stats["ok"] >= next_flush:
                            need_flush = True
                            next_flush += FLUSH_EVERY
                if st == "failed":
                    failures.append(res)
                if done % 50 == 0 or done == len(entries):
                    el = time.time() - t0
                    log(f"... {done}/{len(entries)} ({el:.0f}s) "
                        f"ok={stats['ok']} skip={stats['skipped']} "
                        f"fail={stats['failed']} no_foto={stats['missing']}")
            if need_flush:
                # Salvataggio parziale atomico: anche se la run viene cancellata
                # o il processo ucciso, i ritratti già completati non si ripescano.
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
        live = {f"{e['tour']}/{e['slug']}" for e in entries}
        for key in list(manifest_logos.keys()):
            if key not in live:
                m = manifest_logos.pop(key)
                if m.get("webp_file"):
                    p = os.path.join(args.out, m["webp_file"]["file"])
                    if os.path.exists(p):
                        os.remove(p)
                        pruned += 1
        log(f"Prune: rimossi {pruned} giocatori usciti dalle classifiche.")

    # --- manifesto + indice compatto ------------------------------------------
    os.makedirs(args.out, exist_ok=True)
    write_manifest(args.out, manifest_logos, cfg)
    write_compact_index(args.out, manifest_logos)

    el = time.time() - t0
    log("")
    log(f"FINITO in {el:.0f}s: ok={stats['ok']} saltati={stats['skipped']} "
        f"falliti={stats['failed']} senza_foto={stats['missing']} "
        f"file_scaricati={stats['files']}")
    if stats["missing"]:
        log(f"Nota: {stats['missing']} giocatori non hanno un ritratto su ESPN: "
            f"non sono errori, sono registrati nel manifesto e non verranno "
            f"ritentati (usa --retry-missing per riprovarli).")
    if failures:
        log("Primi errori:")
        for f in failures[:10]:
            log(f"  - {f['key']}: {'; '.join(f['errors'])}")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        per_tour: dict[str, int] = {}
        for m in manifest_logos.values():
            if not m.get("webp_file"):
                continue  # nell'indice per tour solo i ritratti realmente presenti
            tn = m.get("tour_name") or m.get("tour", "?")
            per_tour[tn] = per_tour.get(tn, 0) + 1
        try:
            write_github_summary(summary_path, stats, failures, per_tour)
        except Exception as e:
            log(f"(impossibile scrivere il riepilogo GitHub: {e})")
    return 3 if aborted is not None else 0


if __name__ == "__main__":
    sys.exit(main())
