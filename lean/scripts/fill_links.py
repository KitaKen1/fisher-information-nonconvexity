"""Fill stable proof and Lean4Web links after publication.

Usage (from the repository root, after the commit is public):
    python3 lean/scripts/fill_links.py https://github.com/OWNER/REPO FULL_COMMIT_SHA
It updates the `formal_proof` attribute of the FC statement and the Lean4Web link of
`README.md`.
"""

import argparse
from pathlib import Path
import re
from urllib.parse import quote, urlparse

LEAN = Path(__file__).absolute().parents[1]
ROOT = LEAN.parent
DEFAULT_REPO = "https://github.com/KitaKen1/fisher-information-nonconvexity-lean"

parser = argparse.ArgumentParser()
parser.add_argument("repository", help="Published repository URL, https://github.com/OWNER/REPO")
parser.add_argument("commit", help="Full 40-character commit SHA containing these files")
args = parser.parse_args()
url = urlparse(args.repository.rstrip("/"))
if url.scheme != "https" or url.netloc != "github.com" or url.query or url.fragment or \
        not re.fullmatch(r"/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", url.path):
    parser.error("Use a plain HTTPS GitHub repository URL")
if not re.fullmatch(r"[0-9a-fA-F]{40}", args.commit):
    parser.error("Use a full 40-character commit SHA")
repo = args.repository.rstrip("/")


def line_link(filename, prefix):
    lines = (ROOT / filename).read_text(encoding="utf-8").splitlines()
    line = next(i for i, s in enumerate(lines, 1) if s.startswith(prefix))
    return f"{repo}/blob/{args.commit}/{filename}#L{line}"


proof = line_link("lean/Fisher41/FC/Main.lean", "theorem fisherInformationConvexity :")
variant = line_link("lean/Fisher41/FC/Main.lean",
                    "theorem fisherInformationConvexity.variants.smooth")
paper = line_link("lean/Fisher41/Main/Paper.lean", "theorem paperTheorem1")
raw = f"https://raw.githubusercontent.com{url.path}/{args.commit}/lean4web/Fisher41Lean4Web.lean"
live = "https://live.lean-lang.org/#url=" + quote(raw, safe="")
print(f"FC target proof: {proof}")
print(f"FC variant proof: {variant}")
print(f"Theorem 1 proof: {paper}")
print(f"Lean4Web (select v4.35.0-rc3): {live}")


def update(path, substitutions):
    text = path.read_text(encoding="utf-8")
    text = text.replace(DEFAULT_REPO, repo)
    for pattern, replacement in substitutions:
        text, count = re.subn(pattern, lambda m: m.group(1) + replacement + m.group(2), text)
        if count == 0:
            raise SystemExit(f"No link matched {pattern!r} in {path.name}")
    path.write_text(text, encoding="utf-8")


fc = ROOT / "FClikelean/FisherInformationConvexity.lean"
fc_text = fc.read_text(encoding="utf-8").replace(DEFAULT_REPO, repo)
links = iter([proof, variant])
fc_text, count = re.subn(r'(formal_proof using lean4 at ")[^"]*(")',
                         lambda m: m.group(1) + next(links) + m.group(2), fc_text)
if count != 2:
    raise SystemExit("Expected two formal_proof attributes (main theorem, then variant)")
fc.write_text(fc_text, encoding="utf-8")
update(ROOT / "README.md",
       [(r"(\*\*Try it in Lean4Web:\*\* \[open the complete proof in one file\]\()[^)]*(\))", live)])
update(ROOT / "FClikelean/README.md", [])
print("Updated the FC statement, README.md and FClikelean/README.md.")
