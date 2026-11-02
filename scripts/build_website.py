#!/usr/bin/env python3
"""Build the mathematical website from handwritten pages and the actual Lean statement."""
import html
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAGES = {"index": "Overview", "statement": "Statement", "proof": "Proof guide",
         "library": "Library", "api": "API", "verification": "Verification"}
DECLARATIONS = [
    ("theoremA", "MainTheorems", "Theorem A: a dimension-preserving representation embedding of Kronecker modules"),
    ("corollaryDimension", "MainTheorems", "Corollary 1.1: indecomposable modules of every infinite dimension"),
    ("corollaryRadical", "MainTheorems", "Corollary 5.3: control of the endomorphism ring"),
    ("linesOfEveryLength", "MainTheorems", "Long lines in the universal cover, without the classification of sincere algebras"),
    ("theoremA_of_bongartz", "BongartzTheorem/Reduction/DataForm", "Theorem A from the data form of Bongartz's Theorem 6"),
    ("twistedMulBasisExists", "BongartzTheorem/Reduction/DistributiveCase", "Twisted multiplicative bases of minimal representation-infinite distributive algebras"),
    ("RayCat.pointBrickData", "BongartzTheorem/CriticalPieces/PieceCritical", "Critical pieces carry point-brick data, without tilting theory"),
    ("RayCat.noContour_of_large", "BongartzTheorem/ContourExclusion/ContourFree", "A large sincere directing module excludes contours"),
    ("SplitBasicData.isRepresentationFinite_linearization", "RayCategories/Distributive/LinearizationRepresentationFinite", "Bretscher-Gabriel: the standard form of a representation-finite algebra is representation-finite"),
]


def main():
    subprocess.run(["python3", str(ROOT / "scripts/generate_challenge.py"), "--check"], check=True)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
    repo_url = "https://github.com/haruhisa-enomoto/third-brauer-thrall-conjecture"
    source_url = repo_url + "/blob/" + ("main" if dirty else commit)
    statement = (ROOT / "Challenge.lean").read_text()
    output = ROOT / "_site"
    output.mkdir(exist_ok=True)
    shutil.copytree(ROOT / "website/assets", output / "assets", dirs_exist_ok=True)
    api = ROOT / "docbuild/.lake/build/doc"
    api_state_path = ROOT / "docbuild/.lake/build/api-build.json"
    api_state = json.loads(api_state_path.read_text()) if api_state_path.exists() else {}
    has_api = (api / "index.html").exists() and api_state.get("complete", False)
    if has_api:
        for revisions in ([api_state["source_commit"], "HEAD"], ["HEAD"]):
            subprocess.run(["git", "diff", "--exit-code", *revisions, "--",
                            "LargeIndecomposable.lean", "LargeIndecomposable",
                            "lean-toolchain", "lake-manifest.json"],
                           cwd=ROOT, check=True)
        # A source migration can delete modules; discard stale generated pages.
        if (output / "api").exists():
            shutil.rmtree(output / "api")
        shutil.copytree(api, output / "api")
        for page in (output / "api").rglob("*.html"):
            overview = Path(os.path.relpath(output / "index.html", page.parent)).as_posix()
            page.write_text(page.read_text().replace(
                "<span>Documentation</span>",
                f'<span><a href="{overview}">Third Brauer–Thrall conjecture</a></span>', 1))
    elif (output / "api").exists():
        shutil.rmtree(output / "api")
    status_file = ROOT / "verification-status.json"
    status = json.loads(status_file.read_text()) if status_file.exists() else {}
    rows = []
    for declaration, module, description in DECLARATIONS:
        path = "LargeIndecomposable/" + module
        target = ("api/" + path + ".html#LargeIndecomposable." + declaration) if has_api else source_url + "/" + path + ".lean"
        rows.append(f'<tr><td><a href="{target}"><code>{declaration}</code></a></td><td>{description}</td></tr>')
    replacements = {
        "source_url": source_url,
        "repo_url": repo_url,
        "statement": html.escape(statement),
        "statement_lines": str(len(statement.splitlines())),
        "declaration_rows": "".join(rows),
        "api_link": '<p><a href="api/index.html">Browse and search the generated API</a></p>' if has_api else
                    '<p>The API has not been generated in this preview. Follow <code>docbuild/README.md</code> to build the documentation tool, run <code>python3 scripts/build_api.py</code>, then rebuild this site.</p>',
        "verification_status": html.escape(status.get("summary", "Verification records are available in the repository.")),
    }
    nav = "".join(f'<a href="{slug}.html">{label}</a>' for slug, label in PAGES.items())
    nav += f'<a href="{repo_url}">GitHub</a>'
    revision = f'<a href="{repo_url}/tree/{commit}">{commit[:7]}</a>' + (" (preview)" if dirty else "")
    api_revision = (f' · API: <a href="{repo_url}/tree/{api_state["source_commit"]}">{api_state["source_commit"][:7]}</a>') if has_api else ""
    for slug, title in PAGES.items():
        body = (ROOT / f"website/pages/{slug}.html").read_text()
        for key, value in replacements.items():
            body = body.replace("{{" + key + "}}", value)
        if "{{" in body:
            raise SystemExit(f"Unresolved template value in {slug}")
        page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} · Third Brauer–Thrall conjecture</title><link rel="stylesheet" href="assets/site.css"></head>
<body><a class="skip" href="#main">Skip to content</a><header class="site-header"><nav class="nav" aria-label="Main"><a class="brand" href="index.html">Third Brauer–Thrall conjecture</a>{nav}</nav></header>
<main id="main">{body}</main><footer class="site-footer">Source: {revision}{api_revision}<br>Haruhisa Enomoto · Lean formalization · Apache-2.0</footer></body></html>'''
        (output / f"{slug}.html").write_text(page)
    (output / "build.json").write_text(json.dumps({"commit": commit, "dirty": dirty,
        "api_generated": has_api, "api_source_commit": api_state.get("source_commit") if has_api else None,
        "statement_lines": len(statement.splitlines())}, indent=2) + "\n")
    print(f"Built {len(PAGES)} pages in {output}")


if __name__ == "__main__":
    main()
