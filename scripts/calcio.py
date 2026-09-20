#!/usr/bin/env python3
"""
calcio.py — scarica i loghi da football-logos.cc in modo ordinato.

Sorgente: https://football-logos.cc/image-sitemap.xml.gz
  Mappa ogni pagina-logo al suo PNG nativo (700px, o 1500px per alcuni
  loghi storici) su assets.football-logos.cc.
Per SVG e altre misure PNG, la pagina del logo viene letta per ricavare
gli hash di download (data-svg-hash / <option value="MISURA::HASH">).
Le pagine di storia-logo non hanno download diretti: per quelle viene
salvato il PNG nativo della sitemap e l'SVG è marcato non disponibile.

Struttura prodotta (default: PNG 700px + SVG):

    calcio/
    ├── index.json                  # manifesto: metadati + hash di ogni logo
    ├── italy/
    │   ├── juventus.svg
    │   ├── juventus-700.png
    │   ├── milan.svg
    │   └── milan-700.png
    ├── spain/
    │   └── ...
    └── tournaments/
        └── ...

Esecuzioni incrementali: i loghi già scaricati e invariati vengono saltati
(confronto hash dalla sitemap), quindi le run successive scaricano solo
le novità.

Modalità leggera per app (--webp N): scarica solo il PNG nativo dalla
sitemap (1 richiesta per logo, niente pagina del logo né SVG), lo riduce
a N px e lo salva come WebP in `<paese>/<slug>.webp`. Produce anche
`index.min.json`, un indice compatto pensato per essere letto da un'app
(Android telefono/TV legge i WebP nativamente). In questa modalità serve
Pillow (pip install pillow).

Rispetto anti-sovraccarico: pochi worker, pausa tra le richieste, backoff
con rispetto di Retry-After, pausa globale condivisa sui 429 e stop
automatico se il rate limit diventa persistente.

Esempi:
    python3 scripts/calcio.py                                # tutto
    python3 scripts/calcio.py --countries italy,spain        # filtro paesi
    python3 scripts/calcio.py --countries italy --limit 20   # prova veloce
    python3 scripts/calcio.py --sizes 700,512,256            # più misure PNG
    python3 scripts/calcio.py --no-svg                       # solo PNG
    python3 scripts/calcio.py --force                        # riscarica tutto

Fonte dati: https://football-logos.cc (i marchi restano dei rispettivi proprietari,
vedi https://football-logos.cc/license/ — uso personale/editoriale, non commerciale).
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import random
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

BASE = "https://football-logos.cc"
IMAGE_SITEMAP = f"{BASE}/image-sitemap.xml.gz"
IMAGE_CDN = "https://images.football-logos.cc"

# Header da browser: il CDN images.* richiede Accept di tipo immagine,
# altrimenti risponde 404. Rispettiamo robots.txt (Allow: /) e usiamo
# pochi worker + pause + backoff per non sovraccaricare il sito.
UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
)
PAGE_HEADERS = {
    "User-Agent": UA,
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
}
IMG_HEADERS = {
    "User-Agent": UA,
    "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
}

VALID_SIZES = ("3000", "1500", "700", "512", "256", "128", "64")

RE_IMG_FILE = re.compile(r"^(.+)\.([0-9a-f]{8})\.png$")
RE_SIZE_DIR = re.compile(r"^(\d+)x(\d+)$")
RE_CAT = re.compile(r'data-category-id="([^"]+)"')
RE_LOGO = re.compile(r'data-logo-id="([^"]+)"')
RE_SVG_HASH = re.compile(r'data-svg-hash="([0-9a-f]*)"')
RE_PNG_OPT = re.compile(r'<option\s+value="(\d+)::([0-9a-f]+)"')

PNG_MAGIC = b"\x89PNG\r\n\x1a\n"


class RateLimitExceeded(Exception):
    """Il CDN risponde 429 in modo persistente: meglio fermarsi e riprovare dopo."""


# Pausa globale condivisa tra i thread dopo un HTTP 429: quando il CDN
# ci rallenta, TUTTI i worker si fermano per non peggiorare la situazione.
_rate_lock = threading.Lock()
_rate_cooldown_until = 0.0
_consec_429 = 0
MAX_CONSEC_429 = 20
_abort = threading.Event()


def log(msg: str) -> None:
    print(msg, flush=True)


def sanitize(name: str) -> str:
    return re.sub(r"[^a-zA-Z0-9._-]+", "_", name)


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
                referer: str = "", cfg: dict | None = None) -> bytes:
    """Scarica un URL in memoria con retry + backoff. Solleva l'ultima eccezione.

    I 429 (rate limit) hanno attese più lunghe, rispettano Retry-After e
    attivano una pausa globale per tutti i thread. Dopo troppi 429
    consecutivi solleva RateLimitExceeded per fermare la run.
    """
    global _consec_429
    last_err: Exception | None = None
    h = dict(headers)
    if referer:
        h["Referer"] = referer
    host = urllib.parse.urlparse(url).netloc
    for attempt in range(retries):
        if _abort.is_set():
            raise RateLimitExceeded("run interrotta per rate limit persistente")
        if cfg:
            polite_wait(cfg)
        try:
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                if resp.status != 200:
                    raise urllib.error.HTTPError(url, resp.status, "bad status", resp.headers, None)
                data = resp.read()
                with _rate_lock:
                    _consec_429 = 0
                return data
        except urllib.error.HTTPError as e:
            last_err = e
            if e.code == 429:
                try:
                    retry_after = int(e.headers.get("Retry-After", 0))
                except (TypeError, ValueError):
                    retry_after = 0
                wait = max(5 * (2 ** attempt), retry_after)
                with _rate_lock:
                    _consec_429 += 1
                    trips = _consec_429 >= MAX_CONSEC_429
                _set_cooldown(20)
                log(f"  ... HTTP 429 da {host} (tentativo {attempt + 1}/{retries}), attendo {wait}s")
                if trips:
                    _abort.set()
                    raise RateLimitExceeded(
                        f"rate limit persistente su {host}: "
                        f"{MAX_CONSEC_429} risposte 429 consecutive")
            else:
                wait = 2 ** attempt
            if attempt < retries - 1:
                time.sleep(wait)
        except Exception as e:  # timeout, DNS, reset...
            last_err = e
            if attempt < retries - 1:
                time.sleep(2 ** attempt)
    assert last_err is not None
    raise last_err


def is_valid_png(data: bytes) -> bool:
    return len(data) > 100 and data[:8] == PNG_MAGIC


def is_valid_svg(data: bytes) -> bool:
    head = data[:300].strip().lower()
    return len(data) > 50 and head.startswith(b"<svg") and b"</svg>" in data[-32:].lower()


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


def write_manifest(out_dir: str, sizes: list[str], want_svg: bool, logos: dict,
                   extra: dict | None = None) -> None:
    """Scrive il manifesto in modo atomico (usato anche per i salvataggi parziali)."""
    manifest = {
        "source": IMAGE_SITEMAP,
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "sizes": sizes,
        "svg": want_svg,
        "count": len(logos),
        "logos": dict(sorted(logos.items())),
    }
    if extra:
        manifest.update(extra)
    path = os.path.join(out_dir, "index.json")
    save_file(json.dumps(manifest, ensure_ascii=False, indent=1).encode("utf-8"), path)


def write_compact_index(out_dir: str, logos: dict) -> None:
    """Indice compatto (index.min.json) pensato per le app: una voce per logo
    con nome, paese e file, senza i metadati di scaricamento."""
    compact = {
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "count": len(logos),
        "logos": {
            key: {
                "name": m.get("name", ""),
                "country": m.get("country", ""),
                "slug": m.get("slug", ""),
                "file": (m.get("webp_file") or {}).get("file", ""),
            }
            for key, m in sorted(logos.items())
        },
    }
    path = os.path.join(out_dir, "index.min.json")
    save_file(json.dumps(compact, ensure_ascii=False,
                         separators=(",", ":")).encode("utf-8"), path)


def load_sitemap(timeout: int, retries: int) -> list[dict]:
    log(f"Scarico sitemap immagini: {IMAGE_SITEMAP}")
    raw = fetch_bytes(IMAGE_SITEMAP, PAGE_HEADERS, timeout, retries)
    xml_bytes = gzip.decompress(raw)
    root = ET.fromstring(xml_bytes)
    ns_page = "{http://www.sitemaps.org/schemas/sitemap/0.9}"
    ns_img = "{http://www.google.com/schemas/sitemap-image/1.1}"
    entries: list[dict] = []
    for url_el in root.findall(f"{ns_page}url"):
        page_el = url_el.find(f"{ns_page}loc")
        img_el = url_el.find(f"{ns_img}image/{ns_img}loc")
        title_el = url_el.find(f"{ns_img}image/{ns_img}title")
        if page_el is None or img_el is None:
            continue
        page_url = (page_el.text or "").strip()
        image_url = (img_el.text or "").strip()
        title = (title_el.text or "").strip() if title_el is not None else ""
        parts = page_url.split("/")
        if len(parts) < 5 or not image_url.endswith(".png"):
            continue
        country = parts[3]
        filename = image_url.rsplit("/", 1)[-1]
        size_dir = image_url.rsplit("/", 2)[-2]
        m = RE_IMG_FILE.match(filename)
        ms = RE_SIZE_DIR.match(size_dir)
        if not m or not ms or not country:
            continue
        entries.append(
            {
                "page_url": page_url,
                "image_url": image_url,
                "title": title,
                "country": country,
                "slug": m.group(1),
                "hash": m.group(2),
                "size": ms.group(1),  # es. "700" da "700x700" ("1500" per storici)
            }
        )
    log(f"Sitemap: {len(entries)} loghi trovati.")
    return entries


def parse_logo_page(html: str) -> dict:
    """Estrae category/logo/svg-hash e hash PNG per misura dalla pagina del logo."""
    cat = RE_CAT.search(html)
    logo = RE_LOGO.search(html)
    svg = RE_SVG_HASH.search(html)
    png_hashes = {size: h for size, h in RE_PNG_OPT.findall(html)}
    return {
        "category_id": cat.group(1) if cat else "",
        "logo_id": logo.group(1) if logo else "",
        "svg_hash": svg.group(1) if svg else "",
        "png_hashes": png_hashes,
    }


def process_entry(entry: dict, cfg: dict, manifest_logos: dict) -> dict:
    """Scarica PNG (+SVG) di un logo. Ritorna un dict con l'esito."""
    country = sanitize(entry["country"])
    slug = sanitize(entry["slug"])
    key = f"{entry['country']}/{entry['slug']}"
    out = cfg["out"]
    sizes: list[str] = cfg["sizes"]
    want_svg: bool = cfg["svg"]
    native_size = entry["size"]

    prev = manifest_logos.get(key) if not cfg["force"] else None
    if prev and prev.get("hash") != entry["hash"]:
        prev = None  # logo aggiornato sul sito: riscarica tutto

    # --- skip se già completo (verifica i file registrati nel manifesto) ----
    if prev and prev.get("sizes") == sizes and prev.get("svg") == want_svg and prev.get("png"):
        recorded = list(prev["png"].values())
        if prev.get("svg_file"):
            recorded.append(prev["svg_file"])
        if recorded and all(os.path.exists(os.path.join(out, f["file"])) for f in recorded):
            if (not want_svg) or prev.get("svg_missing") or prev.get("svg_file"):
                return {"key": key, "status": "skipped"}

    errors: list[str] = []
    png_done: dict[str, dict] = {}
    svg_done: dict | None = None
    svg_missing = False
    page_info: dict | None = None
    page_state = "todo"  # todo | ok | no_widget | error

    def ensure_page() -> None:
        nonlocal page_info, page_state
        if page_state != "todo":
            return
        try:
            html = fetch_bytes(entry["page_url"], PAGE_HEADERS,
                               cfg["timeout"], cfg["retries"], cfg=cfg).decode("utf-8", "replace")
        except RateLimitExceeded:
            raise
        except Exception as e:
            page_state = "error"
            errors.append(f"pagina: {e}")
            return
        info = parse_logo_page(html)
        if not info["category_id"] or not info["logo_id"]:
            page_state = "no_widget"  # es. pagine logo-history: nessun download diretto
        else:
            page_state = "ok"
            page_info = info

    def reuse_prev(kind: str, size: str | None, expected_hash: str) -> dict | None:
        """Riusa il file di una run precedente se hash coincide ed esiste."""
        if not prev:
            return None
        if kind == "png":
            rec = prev.get("png", {}).get(size or "", {})
        else:
            rec = prev.get("svg_file") or {}
        if rec and rec.get("hash") == expected_hash \
                and os.path.exists(os.path.join(out, rec["file"])):
            return rec
        return None

    def download_png(url: str, dest_rel: str, expected_hash: str) -> dict:
        data = fetch_bytes(url, IMG_HEADERS, cfg["timeout"], cfg["retries"],
                           referer=entry["page_url"], cfg=cfg)
        if not is_valid_png(data):
            raise ValueError("contenuto non-PNG")
        save_file(data, os.path.join(out, dest_rel))
        return {"hash": expected_hash, "file": dest_rel}

    # --- PNG alla misura nativa della sitemap (URL diretto, no pagina) -------
    for size in sizes:
        if size != native_size:
            continue
        dest_rel = os.path.join(country, f"{slug}-{size}.png")
        rec = reuse_prev("png", size, entry["hash"])
        if rec:
            png_done[size] = rec
            continue
        try:
            png_done[size] = download_png(entry["image_url"], dest_rel, entry["hash"])
        except RateLimitExceeded:
            raise
        except Exception as e:
            errors.append(f"png-{size}: {e}")

    # --- PNG altre misure (via pagina) ----------------------------------------
    need_page_sizes = [s for s in sizes if s != native_size and s not in png_done]
    if need_page_sizes:
        ensure_page()
        if page_state == "ok" and page_info:
            for size in need_page_sizes:
                h = page_info["png_hashes"].get(size, "")
                if not h:
                    errors.append(f"png-{size}: misura non offerta nella pagina")
                    continue
                dest_rel = os.path.join(country, f"{slug}-{size}.png")
                rec = reuse_prev("png", size, h)
                if rec:
                    png_done[size] = rec
                    continue
                url = (f"{IMAGE_CDN}/{page_info['category_id']}/{size}/"
                       f"{page_info['logo_id']}.{h}.png")
                try:
                    png_done[size] = download_png(url, dest_rel, h)
                except RateLimitExceeded:
                    raise
                except Exception as e:
                    errors.append(f"png-{size}: {e}")

    # --- Fallback: PNG nativo della sitemap -----------------------------------
    # Se la pagina non espone download (loghi storici) o una misura richiesta
    # fallisce, salviamo comunque il PNG nativo della sitemap: meglio di niente.
    if native_size not in sizes and native_size not in png_done:
        dest_rel = os.path.join(country, f"{slug}-{native_size}.png")
        rec = reuse_prev("png", native_size, entry["hash"])
        if rec:
            png_done[native_size] = rec
        elif page_state in ("no_widget", "error") or any(x.startswith("png-") for x in errors):
            try:
                png_done[native_size] = download_png(entry["image_url"], dest_rel, entry["hash"])
            except RateLimitExceeded:
                raise
            except Exception as e:
                errors.append(f"png-{native_size} (fallback): {e}")

    # --- SVG ------------------------------------------------------------------
    if want_svg:
        ensure_page()
        if page_state == "ok" and page_info and page_info["svg_hash"]:
            h = page_info["svg_hash"]
            rec = reuse_prev("svg", None, h)
            if rec:
                svg_done = rec
            else:
                url = (f"{IMAGE_CDN}/{page_info['category_id']}/"
                       f"{page_info['logo_id']}.{h}.svg")
                try:
                    data = fetch_bytes(url, IMG_HEADERS, cfg["timeout"], cfg["retries"],
                                       referer=entry["page_url"], cfg=cfg)
                    if not is_valid_svg(data):
                        raise ValueError("contenuto non-SVG")
                    dest_rel = os.path.join(country, f"{slug}.svg")
                    save_file(data, os.path.join(out, dest_rel))
                    svg_done = {"hash": h, "file": dest_rel}
                except RateLimitExceeded:
                    raise
                except Exception as e:
                    errors.append(f"svg: {e}")
        elif page_state == "no_widget" or (page_state == "ok" and page_info
                                           and not page_info["svg_hash"]):
            svg_missing = True  # nessun vettoriale offerto (es. loghi storici)
        else:  # pagina irraggiungibile: riusa l'SVG precedente se invariato
            if prev and prev.get("svg_file") \
                    and os.path.exists(os.path.join(out, prev["svg_file"]["file"])):
                svg_done = prev["svg_file"]
            else:
                errors.append("svg: pagina non leggibile")

    status = "ok" if not errors else ("partial" if (png_done or svg_done) else "failed")
    return {
        "key": key,
        "status": status,
        "errors": errors,
        "manifest": {
            "name": entry["title"] or slug,
            "country": entry["country"],
            "slug": entry["slug"],
            "page_url": entry["page_url"],
            "hash": entry["hash"],       # hash PNG sitemap (rilevatore di modifiche)
            "sizes": sizes,
            "svg": want_svg,
            "svg_missing": svg_missing,
            "png": png_done,
            "svg_file": svg_done,
            "fetched_at": datetime.now(timezone.utc).isoformat(),
        },
    }


def process_entry_webp(entry: dict, cfg: dict, manifest_logos: dict) -> dict:
    """Modalità leggera: PNG nativo -> WebP ridotto (1 sola richiesta HTTP).

    Niente pagina del logo né SVG: il file `<paese>/<slug>.webp` è ideale
    per l'uso runtime in app Android (telefono e TV).
    """
    country = sanitize(entry["country"])
    slug = sanitize(entry["slug"])
    key = f"{entry['country']}/{entry['slug']}"
    out = cfg["out"]
    max_px = cfg["webp"]
    quality = cfg["webp_quality"]

    prev = manifest_logos.get(key) if not cfg["force"] else None
    if prev and prev.get("hash") != entry["hash"]:
        prev = None
    if prev and prev.get("webp") == max_px and prev.get("webp_file"):
        rec = prev["webp_file"]
        if rec.get("hash") == entry["hash"] \
                and os.path.exists(os.path.join(out, rec["file"])):
            return {"key": key, "status": "skipped"}

    dest_rel = os.path.join(country, f"{slug}.webp")
    errors: list[str] = []
    webp_file: dict | None = None
    try:
        data = fetch_bytes(entry["image_url"], IMG_HEADERS, cfg["timeout"],
                           cfg["retries"], referer=entry["page_url"], cfg=cfg)
        if not is_valid_png(data):
            raise ValueError("contenuto non-PNG")
        webp = png_to_webp(data, max_px, quality)
        if not is_valid_webp(webp):
            raise ValueError("conversione WebP fallita")
        save_file(webp, os.path.join(out, dest_rel))
        webp_file = {"hash": entry["hash"], "file": dest_rel}
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
            "name": entry["title"] or slug,
            "country": entry["country"],
            "slug": entry["slug"],
            "page_url": entry["page_url"],
            "hash": entry["hash"],
            "webp": max_px,
            "webp_quality": quality,
            "webp_file": webp_file,
            "sizes": [],
            "svg": False,
            "svg_missing": False,
            "png": {},
            "svg_file": None,
            "fetched_at": datetime.now(timezone.utc).isoformat(),
        },
    }


def write_github_summary(path: str, stats: dict, failures: list[dict],
                         countries: dict, fmt_note: str = "") -> None:
    lines = [
        "## ⚽ Sincronizzazione loghi",
        "",
        f"- Loghi elaborati: **{stats['total']}**",
        f"- Scaricati/aggiornati: **{stats['ok'] + stats['partial']}** "
        f"({stats['files']} file)",
        f"- Saltati (già aggiornati): **{stats['skipped']}**",
        f"- Falliti: **{stats['failed']}**",
        f"- Senza SVG disponibile: **{stats['svg_missing']}**",
        *([f"- Formato: **{fmt_note}**"] if fmt_note else []),
        "",
        "<details><summary>Loghi per paese (top 30)</summary>",
        "",
        "| Paese | Loghi |",
        "|---|---|",
    ]
    for c, n in sorted(countries.items(), key=lambda x: -x[1])[:30]:
        lines.append(f"| {c} | {n} |")
    lines.append("</details>")
    if failures:
        lines += ["", "### ❌ Errori (primi 20)", ""]
        for f in failures[:20]:
            lines.append(f"- `{f['key']}`: {'; '.join(f['errors'])}")
        lines += ["",
                  "> ℹ️ Rilancia il workflow per completare i loghi parziali/falliti: "
                  "i file già scaricati vengono riusati, si scarica solo ciò che manca."]
    lines.append("")
    with open(path, "a", encoding="utf-8") as fh:
        fh.write("\n".join(lines))


def main() -> int:
    ap = argparse.ArgumentParser(description="Scarica i loghi da football-logos.cc in modo ordinato.")
    ap.add_argument("--out", default="calcio", help="Cartella di destinazione (default: calcio)")
    ap.add_argument("--countries", default="",
                    help="Solo questi paesi, separati da virgola (es. italy,spain). Default: tutti.")
    ap.add_argument("--sizes", default="700",
                    help="Misure PNG separate da virgola, tra 3000,1500,700,512,256,128,64 (default: 700)")
    ap.add_argument("--svg", dest="svg", action=argparse.BooleanOptionalAction, default=True,
                    help="Scarica anche gli SVG (default: sì; --no-svg per disattivare)")
    ap.add_argument("--limit", type=int, default=0, help="Scarica al massimo N loghi (0 = tutti)")
    ap.add_argument("--workers", type=int, default=4,
                    help="Download paralleli (default: 4; abbassa se vedi HTTP 429)")
    ap.add_argument("--delay", type=float, default=0.5,
                    help="Pausa in secondi prima di ogni richiesta (default: 0.5; alza se vedi HTTP 429)")
    ap.add_argument("--force", action="store_true", help="Riscarica tutto, anche se presente")
    ap.add_argument("--webp", type=int, default=0,
                    help="Modalità leggera per app: riduce ogni logo a N px di "
                         "lato e salva <paese>/<slug>.webp (es. --webp 512). "
                         "Solo il PNG nativo: 1 richiesta per logo, niente SVG. "
                         "Richiede Pillow. Cambiare N riscarica tutto.")
    ap.add_argument("--webp-quality", type=int, default=80,
                    help="Qualità WebP da 1 a 100 (default: 80)")
    ap.add_argument("--prune", action="store_true",
                    help="Rimuove dal manifesto/file i loghi spariti dalla sitemap (solo run complete)")
    ap.add_argument("--timeout", type=int, default=30, help="Timeout HTTP in secondi (default: 30)")
    ap.add_argument("--retries", type=int, default=3, help="Tentativi per download (default: 3)")
    args = ap.parse_args()

    sizes = [s.strip() for s in args.sizes.split(",") if s.strip()]
    if not sizes or any(s not in VALID_SIZES for s in sizes):
        log(f"ERRORE: --sizes non valido. Scegli tra: {','.join(VALID_SIZES)}")
        return 1
    if args.prune and (args.countries or args.limit):
        log("ERRORE: --prune si può usare solo su run complete (senza --countries/--limit).")
        return 1

    wanted = {c.strip().lower() for c in args.countries.split(",") if c.strip()}

    try:
        entries = load_sitemap(args.timeout, args.retries)
    except Exception as e:
        log(f"ERRORE fatale: impossibile leggere la sitemap: {e}")
        return 1
    if wanted:
        entries = [e for e in entries if e["country"].lower() in wanted]
        log(f"Filtro paesi {sorted(wanted)}: {len(entries)} loghi.")
    entries.sort(key=lambda e: (e["country"], e["slug"]))
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

    webp_mode = args.webp > 0
    svg_effective = False if webp_mode else args.svg
    if webp_mode:
        sizes = []
        log(f"Modalità WebP leggera: 1 richiesta per logo, output "
            f"{args.out}/<paese>/<slug>.webp a {args.webp}px "
            f"(qualità {args.webp_quality}). Opzioni --sizes/--svg ignorate.")
        try:
            import PIL  # noqa: F401
        except ImportError:
            log("ERRORE: la modalità --webp richiede Pillow (pip install pillow).")
            return 1

    cfg = {"out": args.out, "sizes": sizes, "svg": svg_effective, "force": args.force,
           "timeout": args.timeout, "retries": args.retries, "delay": max(0.0, args.delay),
           "webp": args.webp, "webp_quality": max(1, min(100, args.webp_quality))}

    stats = {"total": len(entries), "ok": 0, "partial": 0, "skipped": 0,
             "failed": 0, "files": 0, "svg_missing": 0}
    failures: list[dict] = []
    lock = threading.Lock()
    done = 0
    t0 = time.time()

    workers = max(1, min(args.workers, 16))
    if webp_mode:
        log(f"Avvio download: {len(entries)} loghi, {workers} worker, "
            f"WebP {cfg['webp']}px q{cfg['webp_quality']}, pausa {cfg['delay']}s.")
        per_logo = 1  # solo il PNG nativo, niente pagina del logo né SVG
    else:
        log(f"Avvio download: {len(entries)} loghi, {workers} worker, "
            f"misure PNG {','.join(sizes)}, SVG {'sì' if svg_effective else 'no'}, "
            f"pausa {cfg['delay']}s.")
        per_logo = 2 if not svg_effective else 3  # stima richieste HTTP per logo
    est_min = len(entries) * per_logo * cfg["delay"] * 1.25 / workers / 60
    if len(entries) > 0:
        log(f"Stima indicativa: ~{max(1, est_min):.0f} minuti "
            f"(dipende dalla velocità di risposta del CDN).")

    FLUSH_EVERY = 50  # salva il manifesto ogni N loghi scaricati: se la run
    next_flush = FLUSH_EVERY  # viene interrotta, i progressi restano salvati
    extra_hdr = ({"webp": cfg["webp"], "webp_quality": cfg["webp_quality"]}
                 if webp_mode else None)

    aborted: Exception | None = None
    pool = ThreadPoolExecutor(max_workers=workers)
    try:
        worker_fn = process_entry_webp if webp_mode else process_entry
        futs = {pool.submit(worker_fn, e, cfg, manifest_logos): e for e in entries}
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
                if st in ("ok", "partial"):
                    m = res["manifest"]
                    manifest_logos[res["key"]] = m
                    stats["files"] += (len(m["png"]) + (1 if m.get("webp_file") else 0)
                                       + (1 if m["svg_file"] else 0))
                    if m["svg_missing"]:
                        stats["svg_missing"] += 1
                    if stats["ok"] + stats["partial"] >= next_flush:
                        need_flush = True
                        next_flush += FLUSH_EVERY
                if st in ("partial", "failed"):
                    failures.append(res)
                if done % 50 == 0 or done == len(entries):
                    el = time.time() - t0
                    log(f"... {done}/{len(entries)} ({el:.0f}s) "
                        f"ok={stats['ok']} skip={stats['skipped']} fail={stats['failed']}")
            if need_flush:
                # Salvataggio parziale atomico: anche se la run viene cancellata
                # o il processo ucciso, i loghi già completati non si ripescano.
                write_manifest(args.out, sizes, svg_effective, manifest_logos, extra_hdr)
    finally:
        pool.shutdown(wait=False, cancel_futures=True)

    if aborted is not None:
        log("")
        log(f"INTERROTTO: {aborted}")
        log("Il CDN sta limitando le richieste in modo persistente. I progressi parziali")
        log("sono salvati nel manifesto: rilancia più tardi (eventualmente con --delay")
        log("più alto o --workers più basso) per completare i loghi mancanti.")

    # --- prune (solo run complete non interrotte) ------------------------------
    pruned = 0
    if args.prune and aborted is None:
        live = {f"{e['country']}/{e['slug']}" for e in entries}
        for key in list(manifest_logos.keys()):
            if key not in live:
                m = manifest_logos.pop(key)
                for pf in list(m.get("png", {}).values()):
                    p = os.path.join(args.out, pf["file"])
                    if os.path.exists(p):
                        os.remove(p)
                        pruned += 1
                if m.get("svg_file"):
                    p = os.path.join(args.out, m["svg_file"]["file"])
                    if os.path.exists(p):
                        os.remove(p)
                        pruned += 1
                if m.get("webp_file"):
                    p = os.path.join(args.out, m["webp_file"]["file"])
                    if os.path.exists(p):
                        os.remove(p)
                        pruned += 1
        log(f"Prune: rimosse {pruned} file non più in sitemap.")

    # --- manifesto ------------------------------------------------------------
    os.makedirs(args.out, exist_ok=True)
    write_manifest(args.out, sizes, svg_effective, manifest_logos, extra_hdr)
    if webp_mode:
        write_compact_index(args.out, manifest_logos)

    el = time.time() - t0
    log("")
    log(f"FINITO in {el:.0f}s: ok={stats['ok']} parziali={stats['partial']} "
        f"saltati={stats['skipped']} falliti={stats['failed']} "
        f"file_scaricati={stats['files']} senza_svg={stats['svg_missing']}")
    if failures:
        log("Primi errori:")
        for f in failures[:10]:
            log(f"  - {f['key']}: {'; '.join(f['errors'])}")

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        countries: dict[str, int] = {}
        for m in manifest_logos.values():
            countries[m["country"]] = countries.get(m["country"], 0) + 1
        fmt_note = (f"WebP {cfg['webp']}px qualità {cfg['webp_quality']}"
                    if webp_mode else "")
        try:
            write_github_summary(summary_path, stats, failures, countries, fmt_note)
        except Exception as e:
            log(f"(impossibile scrivere il riepilogo GitHub: {e})")
    return 3 if aborted is not None else 0


if __name__ == "__main__":
    sys.exit(main())
