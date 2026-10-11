"""Build the complete proof and the Lean4Web file, and audit the FC-style statement.

Run from the repository root: `python3 lean/scripts/build_audit.py`.
Set `FC_DIR` to a built Formal Conjectures checkout to also compile
`FClikelean/FisherInformationConvexity.lean` with the Formal Conjectures linters. If the
checkout's own packages are not built, set `FC_DEPS_DIR` to a project whose `lake-manifest.json`
pins the same dependency revisions and whose packages are built; their build directories are
then used together with the checkout's `FormalConjecturesUtil`.
Results are written to `lean/evidence/build.log` and `lean/evidence/build_results.json`.
"""

from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time

LEAN = Path(__file__).absolute().parents[1]
ROOT = LEAN.parent
FC = ROOT / "FClikelean" / "FisherInformationConvexity.lean"
WEB_DIR = ROOT / "lean4web"
WEB = WEB_DIR / "Fisher41Lean4Web.lean"
EVIDENCE = LEAN / "evidence"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = ["fisherInformationConvexity", "fisherInformationConvexity.variants.smooth"]
FINAL = ["Fisher41.paperTheorem1", "Fisher41.pdfMain", "Fisher41.fisherSecondDerivNeg",
         "Fisher41.fisherNonconvex", "Arxiv.«2605.18081».fisherInformationConvexity",
         "Arxiv.«2605.18081».fisherInformationConvexity.variants.smooth"]
FC_LINTERS = ["namespace", "stubs", "openClassical", "ams_attribute", "category_attribute",
              "category_answer", "category_docstring", "conditional_formal_proof",
              "moduleDocstring", "latex_docstring", "imports", "existsImplication"]


def require(condition, message):
    if not condition:
        raise SystemExit(f"AUDIT FAILED: {message}")


def definitions(text):
    """The definition block of the FC statement (from `heatFlow` up to the question)."""
    start = text.index("/-- The heat flow")
    ends = [i for i in (text.find("\n/-- Is the Fisher information", start),
                        text.find("\nend Arxiv.«2605.18081»", start)) if i != -1]
    return text[start:min(ends)].strip()


def target(text, name):
    match = re.search(r"theorem " + re.escape(name) + r"\s*:\s*([\s\S]*?)\s*:= by", text)
    require(match is not None, f"Missing the Formal Conjectures target theorem {name}")
    return re.sub(r"\s+", " ", match.group(1)).strip()


def uncomment(text):
    result, depth, pos = [], 0, 0
    while pos < len(text):
        if text.startswith("/-", pos):
            depth, pos = depth + 1, pos + 2
        elif depth and text.startswith("-/", pos):
            depth, pos = depth - 1, pos + 2
        elif depth:
            pos += 1
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = len(text) if end == -1 else end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == "\\":
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
        else:
            result.append(text[pos])
            pos += 1
    require(depth == 0, "Unclosed comment")
    return "".join(result)


# Static checks: verbatim definitions, identical statements, no holes.
statement = FC.read_text(encoding="utf-8")
fc_copy = (LEAN / "Fisher41/FC/Statement.lean").read_text(encoding="utf-8")
fc_main = (LEAN / "Fisher41/FC/Main.lean").read_text(encoding="utf-8")
web = WEB.read_text(encoding="utf-8")
require(definitions(statement) == definitions(fc_copy),
        "Definitions differ between FClikelean and lean/Fisher41/FC/Statement.lean")
require(definitions(statement) in web, "The Lean4Web file lacks the FC definitions")
for name in TARGETS:
    require(target(statement, name) == target(fc_main, name) == target(web, name),
            f"Target statements differ: {name}")
sources = [LEAN / "Fisher41.lean", *sorted((LEAN / "Fisher41").rglob("*.lean")), WEB]
for path in sources:
    require(not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|opaque|constant)\b",
                          uncomment(path.read_text(encoding="utf-8"))),
            f"Proof hole or custom axiom: {path}")
require("sorry" in uncomment(statement), "The FC statement should be stated `by sorry`")

EVIDENCE.mkdir(exist_ok=True)
start = time.monotonic()
results, outputs = {}, {}
fc_dir = os.environ.get("FC_DIR")
fc_commit = None


def clean(text):
    text = text.replace(str(ROOT), ".").replace(str(LEAN.resolve()), "./lean")
    if fc_dir:
        text = text.replace(str(Path(fc_dir)), "<FC_DIR>")
    return text.replace(str(Path.home()), "~")


with (EVIDENCE / "build.log").open("w", encoding="utf-8") as log:
    def run(label, args, cwd, env=None):
        log.write(f"\n{label}: {clean(' '.join(args))}\n")
        log.flush()
        t0 = time.monotonic()
        proc = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
        output = clean(proc.stdout + proc.stderr)
        log.write(output)
        log.write(f"Exit code: {proc.returncode} ({time.monotonic() - t0:.0f}s)\n")
        log.flush()
        results[label] = proc.returncode
        outputs[label] = output
        print(f"{label}: exit {proc.returncode} ({time.monotonic() - t0:.0f}s)", flush=True)
        if proc.returncode:
            print(output[-4000:], flush=True)
        return proc

    run("main_proof", ["lake", "build", "Fisher41"], LEAN)
    if results["main_proof"] == 0:
        run("main_axioms", ["lake", "env", "lean", "scripts/Axioms.lean"], LEAN)
    if (WEB_DIR / ".lake").is_dir():
        run("lean4web", ["lake", "build", "Fisher41Lean4Web"], WEB_DIR)
    else:
        # Same Lean and Mathlib revisions as the lean4web project, without a second Mathlib.
        run("lean4web", ["lake", "env", "lean", str(WEB)], LEAN)
    if fc_dir:
        fc_commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=fc_dir, text=True,
                                   capture_output=True).stdout.strip()
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / FC.name
            shutil.copy(FC, copy)
            flags = ["-DautoImplicit=false", "-Dwarn.sorry=false", "-DwarningAsError=true"]
            flags += [f"-Dweak.linter.style.{name}=true" for name in FC_LINTERS]
            fc_deps = os.environ.get("FC_DEPS_DIR")
            if fc_deps:
                def pins(project):
                    data = json.loads((Path(project) / "lake-manifest.json").read_text())
                    return {p["name"]: p["rev"] for p in data["packages"]}
                require(pins(fc_dir) == pins(fc_deps), "FC_DEPS_DIR pins other revisions")
                toolchain = (Path(fc_dir) / "lean-toolchain").read_text().strip()
                lean = (Path.home() / ".elan" / "toolchains" /
                        toolchain.replace("/", "--").replace(":", "---") / "bin" / "lean")
                paths = sorted((Path(fc_deps) / ".lake" / "packages").glob("*/.lake/build/lib/lean"))
                paths.append(Path(fc_dir) / ".lake" / "build" / "lib" / "lean")
                env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
                run("fc_statement", [str(lean), *flags, "-R", tmp, str(copy)], fc_dir, env)
            else:
                run("fc_statement", ["lake", "env", "lean", *flags, "-R", tmp, str(copy)], fc_dir)

axioms = {}
for label, output in outputs.items():
    axioms[label] = {name: [v.strip() for v in values.split(",") if v.strip()]
                     for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                                                    output)}
required = {"main_axioms": FINAL,
            "lean4web": ["Fisher41.paperTheorem1", *FINAL[-2:]]}
axiom_ok = all(name in axioms.get(label, {}) and set(axioms[label][name]) <= ALLOWED
               for label, names in required.items() for name in names)
labels = ["main_proof", "main_axioms", "lean4web"] + (["fc_statement"] if fc_dir else [])
ok = all(results.get(label) == 0 for label in labels) and axiom_ok
result = {
    "status": "PASS" if ok else "FAIL",
    "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "exit_codes": results,
    "elapsed_seconds": round(time.monotonic() - start, 2),
    "timing_note": "Includes dependency loading; modules already built are replayed.",
    "lean_version": (LEAN / "lean-toolchain").read_text().strip(),
    "lean4web_version": (WEB_DIR / "lean-toolchain").read_text().strip(),
    "lean4web_checked_with": "lean4web project" if (WEB_DIR / ".lake").is_dir()
                             else "lake env lean in lean/ (same Lean and Mathlib revisions)",
    "fc_statement_checked_with": f"Formal Conjectures {fc_commit}" if fc_commit else None,
    "axiom_audit_passed": axiom_ok,
    "axioms": {label: {name: axioms.get(label, {}).get(name) for name in names}
               for label, names in required.items()},
    "definitions_and_statements_match": True,
    "no_holes_or_custom_axioms": True,
    "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in [*sources, FC]},
}
(EVIDENCE / "build_results.json").write_text(
    json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": result["status"], "exit_codes": results,
                  "axiom_audit_passed": axiom_ok}))
raise SystemExit(0 if ok else 1)
