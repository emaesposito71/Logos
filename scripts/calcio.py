#!/usr/bin/env python3
"""
calcio.py — scarica i loghi da football-logos.cc in modo ordinato.

Sorgente: https://football-logos.cc/image-sitemap.xml.gz
  Mappa ogni pagina-logo al suo PNG 700px su assets.football-logos.cc.
Per SVG e altre misure PNG, la pagina del logo viene letta per ricavare
gli hash di download (data-svg-hash / <option value="MISURA::HASH">).

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
le novità. Solo stdlib, nessuna dipendenza da installare.

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
import re
import sys
import threading
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone

BASE = "https://football-logos.cc"
IMAGE_SITEMAP = f"{BASE}/image-sitemap.xml.gz"
IMAGE_CDN = "https://images.football-logos.cc"

# Header da browser: il CDN images.* richiede Accept di tipo immagine,
# altrimenti risponde 404. Rispettiamo robots.txt (Allow: /) e usiamo
# pochi worker + retry con backoff per non sovraccaricare il sito.
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


def log(msg: str) -> None:
    print(msg, flush=True)


def sanitize(name: str) -> str:
    return re.sub(r"[^a-zA-Z0-9._-]+", "_", name)


def fetch_bytes(url: str, headers: dict, timeout: int, retries: int, referer: str = "") -> bytes:
    """Scarica un URL in memoria con retry + backoff. Solleva l'ultima eccezione."""
    last_err: Exception | None = None
    h = dict(headers)
    if referer:
        h["Referer"] = referer
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                if resp.status != 200:
                    raise urllib.error.HTTPError(url, resp.status, "bad status", resp.headers, None)
                return resp.read()
        except urllib.error.HTTPError as e:
            last_err = e
            wait = 2 ** attempt
            if e.code == 429:
                try:
                    wait = max(wait, int(e.headers.get("Retry-After", wait)))
                except (TypeError, ValueError):
                    pass
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


def save_file(data: bytes, path: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".part"
    with open(tmp, "wb") as f:
        f.write(data)
    os.replace(tmp, path)


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
                "size": ms.group(1),  # es. "700" da "700x700"
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

    png_files = {s: os.path.join(out, country, f"{slug}-{s}.png") for s in sizes}
    svg_file = os.path.join(out, country, f"{slug}.svg")

    # --- skip se già presente e invariato ----------------------------------
    if not cfg["force"]:
        prev = manifest_logos.get(key)
        if prev and prev.get("hash") == entry["hash"] and prev.get("sizes") == sizes \
                and prev.get("svg") == want_svg:
            if all(os.path.exists(p) for p in png_files.values()) \
                    and (not want_svg or prev.get("svg_missing") or os.path.exists(svg_file)):
                return {"key": key, "status": "skipped"}

    errors: list[str] = []
    png_done: dict[str, dict] = {}
    svg_done: dict | None = None
    svg_missing = False
    page: dict | None = None

    def ensure_page() -> dict | None:
        nonlocal page
        if page is None:
            try:
                html = fetch_bytes(
                    entry["page_url"], PAGE_HEADERS, cfg["timeout"], cfg["retries"]
                ).decode("utf-8", "replace")
                page = parse_logo_page(html)
                if not page["category_id"] or not page["logo_id"]:
                    raise ValueError("attributi data-* non trovati nella pagina")
            except Exception as e:
                errors.append(f"pagina: {e}")
                page = {}
        return page or None

    # --- PNG ---------------------------------------------------------------
    for size in sizes:
        dest = png_files[size]
        try:
            if size == entry["size"]:
                # URL diretto dalla sitemap, nessuna pagina da leggere
                url = entry["image_url"]
                data = fetch_bytes(url, IMG_HEADERS, cfg["timeout"], cfg["retries"],
                                   referer=entry["page_url"])
                if not is_valid_png(data):
                    raise ValueError("contenuto non-PNG")
                save_file(data, dest)
                png_done[size] = {"hash": entry["hash"], "file": os.path.relpath(dest, out)}
            else:
                info = ensure_page()
                h = (info or {}).get("png_hashes", {}).get(size, "")
                if not h:
                    raise ValueError(f"hash PNG {size}px non trovato nella pagina")
                url = f"{IMAGE_CDN}/{info['category_id']}/{size}/{info['logo_id']}.{h}.png"
                data = fetch_bytes(url, IMG_HEADERS, cfg["timeout"], cfg["retries"],
                                   referer=entry["page_url"])
                if not is_valid_png(data):
                    raise ValueError("contenuto non-PNG")
                save_file(data, dest)
                png_done[size] = {"hash": h, "file": os.path.relpath(dest, out)}
        except Exception as e:
            errors.append(f"png-{size}: {e}")

    # --- SVG ---------------------------------------------------------------
    if want_svg:
        try:
            info = ensure_page()
            if not info or not info.get("svg_hash"):
                svg_missing = True  # nessun vettoriale per questo logo (normale)
            else:
                url = f"{IMAGE_CDN}/{info['category_id']}/{info['logo_id']}.{info['svg_hash']}.svg"
                data = fetch_bytes(url, IMG_HEADERS, cfg["timeout"], cfg["retries"],
                                   referer=entry["page_url"])
                if not is_valid_svg(data):
                    raise ValueError("contenuto non-SVG")
                save_file(data, svg_file)
                svg_done = {"hash": info["svg_hash"], "file": os.path.relpath(svg_file, out)}
        except Exception as e:
            errors.append(f"svg: {e}")

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


def write_github_summary(path: str, stats: dict, failures: list[dict], countries: dict) -> None:
    lines = [
        "## ⚽ Sincronizzazione loghi",
        "",
        f"- Loghi elaborati: **{stats['total']}**",
        f"- Scaricati/aggiornati: **{stats['ok'] + stats['partial']}** "
        f"({stats['files']} file)",
        f"- Saltati (già aggiornati): **{stats['skipped']}**",
        f"- Falliti: **{stats['failed']}**",
        f"- Senza SVG disponibile: **{stats['svg_missing']}**",
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
    ap.add_argument("--workers", type=int, default=8, help="Download paralleli (default: 8)")
    ap.add_argument("--force", action="store_true", help="Riscarica tutto, anche se presente")
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

    cfg = {"out": args.out, "sizes": sizes, "svg": args.svg, "force": args.force,
           "timeout": args.timeout, "retries": args.retries}

    stats = {"total": len(entries), "ok": 0, "partial": 0, "skipped": 0,
             "failed": 0, "files": 0, "svg_missing": 0}
    failures: list[dict] = []
    lock = threading.Lock()
    done = 0
    t0 = time.time()

    workers = max(1, min(args.workers, 32))
    log(f"Avvio download: {len(entries)} loghi, {workers} worker, "
        f"misure PNG {','.join(sizes)}, SVG {'sì' if args.svg else 'no'}.")

    with ThreadPoolExecutor(max_workers=workers) as pool:
        futs = {pool.submit(process_entry, e, cfg, manifest_logos): e for e in entries}
        for fut in as_completed(futs):
            res = fut.result()
            with lock:
                done += 1
                st = res["status"]
                stats[st] = stats.get(st, 0) + 1
                if st in ("ok", "partial"):
                    m = res["manifest"]
                    manifest_logos[res["key"]] = m
                    stats["files"] += len(m["png"]) + (1 if m["svg_file"] else 0)
                    if m["svg_missing"]:
                        stats["svg_missing"] += 1
                if st in ("partial", "failed"):
                    failures.append(res)
                if done % 100 == 0 or done == len(entries):
                    el = time.time() - t0
                    log(f"... {done}/{len(entries)} ({el:.0f}s) "
                        f"ok={stats['ok']} skip={stats['skipped']} fail={stats['failed']}")

    # --- prune ---------------------------------------------------------------
    pruned = 0
    if args.prune:
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
        log(f"Prune: rimosse {pruned} file non più in sitemap.")

    # --- manifesto ------------------------------------------------------------
    os.makedirs(args.out, exist_ok=True)
    manifest = {
        "source": IMAGE_SITEMAP,
        "updated_at": datetime.now(timezone.utc).isoformat(),
        "sizes": sizes,
        "svg": args.svg,
        "count": len(manifest_logos),
        "logos": dict(sorted(manifest_logos.items())),
    }
    save_file(json.dumps(manifest, ensure_ascii=False, indent=1).encode("utf-8"), manifest_path)

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
        try:
            write_github_summary(summary_path, stats, failures, countries)
        except Exception as e:
            log(f"(impossibile scrivere il riepilogo GitHub: {e})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
