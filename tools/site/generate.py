#!/usr/bin/env python3
"""Build and validate the standalone ProCGroups documentation site."""

from __future__ import annotations

from html import escape
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import tempfile
from typing import Any
from urllib.parse import quote

import build_site


ROOT = Path(__file__).resolve().parent
CONFIG_PATH = ROOT / "site_config.json"
CHECKER_PATH = ROOT / "tools" / "check_generated_site.py"
SITE_MANIFEST = ".site-manifest.json"
COMPONENT = "ProCGroups"
SEARCH_PREFIX = "window.LEAN_DOCS_INDEX="
TREE_PREFIX = "window.LEAN_DOCS_TREE="

NOTICE_CSS = """

/* ProCGroups release identity and responsibility notice. */
.release-line {
  display: flex;
  align-items: center;
  gap: .7rem;
  margin: -.15rem 0 1.15rem;
  color: var(--muted);
}
.release-badge {
  display: inline-flex;
  align-items: center;
  min-height: 1.75rem;
  padding: .15rem .65rem;
  border: 1px solid var(--border);
  border-radius: 999px;
  background: var(--panel);
  color: var(--text);
  font-size: .86rem;
  font-weight: 700;
  letter-spacing: .04em;
}
.responsibility-notice {
  margin: 0 0 1.5rem;
  padding: 1rem 1.1rem;
  border: 1px solid #d7a72d;
  border-left-width: .35rem;
  border-radius: .45rem;
  background: #fff8df;
  color: #3d3218;
}
.responsibility-notice h2 {
  margin: 0 0 .45rem;
  font-size: 1.05rem;
}
.responsibility-notice p {
  margin: .35rem 0 0;
}
@media (prefers-color-scheme: dark) {
  .responsibility-notice {
    border-color: #b88a24;
    background: #312a18;
    color: #f5e8c4;
  }
}
"""


def load_config() -> dict[str, Any]:
    data = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    required = {
        "schema_version",
        "title",
        "version",
        "source_repository",
        "source_commit",
        "generated_at",
        "source_root",
        "output_root",
        "documentation_url",
        "library_id",
        "library_name",
        "root_import",
        "expected_module_count",
    }
    if not isinstance(data, dict) or set(data) != required:
        raise ValueError("site_config.json does not match the publisher schema")
    if data["schema_version"] != 1:
        raise ValueError("unsupported site_config.json schema version")
    if data["version"] != "v2":
        raise ValueError("the ProCGroups release label must be v2")
    if data["source_repository"] != "https://github.com/n-yamaguchi-0729/ProCGroups":
        raise ValueError("the source repository must be the standalone ProCGroups project")
    if not re.fullmatch(r"[0-9a-f]{40}", data["source_commit"]):
        raise ValueError("source_commit must be a full Git SHA")
    if data["library_id"] != COMPONENT or data["root_import"] != COMPONENT:
        raise ValueError("the public library identity must be ProCGroups")
    if not isinstance(data["expected_module_count"], int) or data["expected_module_count"] <= 0:
        raise ValueError("expected_module_count must be a positive integer")
    return data


def resolve_config_path(raw: str) -> Path:
    path = Path(raw)
    return (ROOT / path).resolve() if not path.is_absolute() else path.resolve()


def collect_procgroups_modules(source_root: Path, expected_count: int) -> dict[str, str]:
    if source_root.is_symlink() or not source_root.is_dir():
        raise ValueError(f"Lean source root is missing or unsafe: {source_root}")
    root_module = source_root / "ProCGroups.lean"
    subtree = source_root / "ProCGroups"
    if (
        root_module.is_symlink()
        or not root_module.is_file()
        or subtree.is_symlink()
        or not subtree.is_dir()
    ):
        raise ValueError("ProCGroups.lean and the ProCGroups source subtree are required")

    selected = [root_module, *sorted(subtree.rglob("*.lean"))]
    all_lean = sorted(source_root.rglob("*.lean"))
    if any(path.is_symlink() or not path.is_file() for path in all_lean):
        raise ValueError("the Lean source tree contains a symlink or non-file source")
    unexpected = sorted(set(all_lean) - set(selected))
    if unexpected:
        shown = ", ".join(path.relative_to(source_root).as_posix() for path in unexpected[:10])
        raise ValueError(f"the standalone source contains non-ProCGroups Lean files: {shown}")
    if len(selected) != expected_count:
        raise ValueError(
            f"expected {expected_count} ProCGroups modules, found {len(selected)}"
        )

    mapping: dict[str, str] = {}
    for path in selected:
        relative = path.relative_to(source_root)
        module = ".".join(relative.with_suffix("").parts)
        if module in mapping:
            raise ValueError(f"duplicate Lean module: {module}")
        mapping[module] = COMPONENT
    if any(
        module != COMPONENT and not module.startswith(COMPONENT + ".")
        for module in mapping
    ):
        raise ValueError("the module inventory escapes the ProCGroups namespace")
    return mapping


def decorate_site(staging: Path, config: dict[str, Any]) -> None:
    index_path = staging / "index.html"
    index = index_path.read_text(encoding="utf-8")
    title_marker = f'<h1 class="page-title">{escape(config["title"])}</h1>'
    if index.count(title_marker) != 1:
        raise ValueError("cannot locate the generated homepage title")
    release_and_notice = f"""\
{title_marker}
  <p class="release-line"><span class="release-badge">{escape(config["version"])}</span><span>Standalone ProCGroups release</span></p>
  <aside class="responsibility-notice" lang="ja" role="note" aria-labelledby="responsibility-title">
    <h2 id="responsibility-title">ご利用にあたって</h2>
    <p><strong>作者はこの分野の専門家ではなく、AIをアシスタントとして利用しています。</strong></p>
    <p>内容の正確性や完全性は保証されません。利用・検証はご自身の責任で行ってください。質問にはお答えできません。</p>
  </aside>"""
    index = index.replace(title_marker, release_and_notice)
    index_path.write_text(index, encoding="utf-8", newline="\n")

    stylesheet = staging / "assets" / "site.css"
    css = stylesheet.read_text(encoding="utf-8").rstrip() + NOTICE_CSS
    stylesheet.write_text(css.rstrip() + "\n", encoding="utf-8", newline="\n")


def inventory_files(root: Path) -> set[str]:
    files: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"generated site contains a symlink: {path}")
        if path.is_file():
            files.add(path.relative_to(root).as_posix())
    return files


def write_manifest(staging: Path, generated_at: str) -> None:
    files = inventory_files(staging)
    files.add(SITE_MANIFEST)
    data = {
        "version": 1,
        "generated_at": generated_at,
        "file_count": len(files),
        "files": sorted(files),
    }
    (staging / SITE_MANIFEST).write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def load_window_json(path: Path, prefix: str) -> list[dict[str, Any]]:
    text = path.read_text(encoding="utf-8").strip()
    if not text.startswith(prefix) or not text.endswith(";"):
        raise ValueError(f"invalid generated JavaScript assignment: {path.name}")
    value = json.loads(text[len(prefix):-1])
    if not isinstance(value, list):
        raise ValueError(f"generated JavaScript value must be an array: {path.name}")
    return value


def collect_tree_modules(nodes: list[dict[str, Any]]) -> set[str]:
    modules: set[str] = set()
    for node in nodes:
        children = node.get("c")
        module = node.get("m")
        if isinstance(children, list):
            modules.update(collect_tree_modules(children))
        elif isinstance(module, str):
            modules.add(module)
    return modules


def load_checker() -> Any:
    spec = importlib.util.spec_from_file_location("procgroups_site_checker", CHECKER_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load the generated-site checker")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def validate_site(
    staging: Path,
    config: dict[str, Any],
    module_components: dict[str, str],
) -> None:
    checker = load_checker()
    errors = checker.check_root(staging)
    if errors:
        raise ValueError("generated-site validation failed:\n" + "\n".join(errors))

    expected_modules = set(module_components)
    build_info = json.loads((staging / "build-info.json").read_text(encoding="utf-8"))
    expected_library = [{
        "id": COMPONENT,
        "display_name": config["library_name"],
        "import": config["root_import"],
        "module_roots": [COMPONENT],
        "module_count": len(expected_modules),
    }]
    expected_metadata = {
        "siteTitle": config["title"],
        "version": config["version"],
        "commit": config["source_commit"],
        "sourceRef": config["source_commit"],
        "sourceRepository": config["source_repository"],
        "libraries": expected_library,
    }
    for key, expected in expected_metadata.items():
        if build_info.get(key) != expected:
            raise ValueError(f"build-info.json has an inconsistent {key}")

    search = load_window_json(staging / "assets" / "search-index.js", SEARCH_PREFIX)
    search_modules = {
        item.get("n")
        for item in search
        if item.get("k") == "Lean file" and isinstance(item.get("n"), str)
    }
    if search_modules != expected_modules:
        raise ValueError("search-index.js does not contain exactly the ProCGroups modules")

    tree = load_window_json(staging / "assets" / "tree-data.js", TREE_PREFIX)
    if len(tree) != 1 or tree[0].get("n") != COMPONENT:
        raise ValueError("tree-data.js must have one ProCGroups library root")
    if collect_tree_modules(tree) != expected_modules:
        raise ValueError("tree-data.js does not contain exactly the ProCGroups modules")

    manifest = json.loads((staging / SITE_MANIFEST).read_text(encoding="utf-8"))
    files = inventory_files(staging)
    if manifest.get("file_count") != len(files) or set(manifest.get("files", [])) != files:
        raise ValueError(".site-manifest.json is not an exhaustive site inventory")

    allowed_fixed = {
        SITE_MANIFEST,
        "index.html",
        "build-info.json",
        "find/index.html",
        "assets/search-index.js",
        "assets/site.css",
        "assets/site.js",
        "assets/tree-data.js",
    }
    unexpected_files = {
        relative
        for relative in files
        if relative not in allowed_fixed
        and not (
            relative.startswith(f"library/{COMPONENT}/")
            and relative.endswith(".html")
        )
    }
    if unexpected_files:
        raise ValueError(
            "generated site contains non-public files: "
            + ", ".join(sorted(unexpected_files)[:20])
        )

    index = (staging / "index.html").read_text(encoding="utf-8")
    required_notice = (
        "作者はこの分野の専門家ではなく",
        "AIをアシスタントとして利用しています",
        "ご自身の責任",
        "質問にはお答えできません",
    )
    if any(text not in index for text in required_notice):
        raise ValueError("the Japanese responsibility notice is incomplete")
    if config["version"] not in index:
        raise ValueError("the homepage does not display the v2 release label")

    text_files = [
        path
        for path in staging.rglob("*")
        if path.is_file() and path.suffix.lower() in {".html", ".js", ".json", ".css"}
    ]
    for path in text_files:
        text = path.read_text(encoding="utf-8")
        if "YamaLean4Lib" in text:
            raise ValueError(f"legacy YamaLean4Lib reference remains in {path}")
        if "/library/CrowellExactSequence/" in text:
            raise ValueError("CrowellExactSequence was incorrectly published as a separate library")
        for match in re.finditer(
            r"https://github\.com/n-yamaguchi-0729/[A-Za-z0-9_.-]+",
            text,
        ):
            if match.group(0) != config["source_repository"]:
                raise ValueError(f"wrong GitHub project link in {path}: {match.group(0)}")


def synchronize_exact(staging: Path, output: Path) -> tuple[int, int]:
    output = output.resolve()
    if (
        output.name != "ProCGroups_pages"
        or output.parent.name != "n-yamaguchi-0729.github.io"
    ):
        raise ValueError(f"refusing unexpected output directory: {output}")
    if output == Path(output.anchor) or output.is_symlink():
        raise ValueError(f"refusing unsafe output directory: {output}")

    source_files = inventory_files(staging)
    output.mkdir(parents=True, exist_ok=True)
    destination_files = inventory_files(output)
    copied = 0
    for relative in sorted(source_files):
        source = staging / PurePosixPath(relative)
        destination = output / PurePosixPath(relative)
        if destination.is_file() and destination.read_bytes() == source.read_bytes():
            continue
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
        copied += 1

    removed = 0
    for relative in sorted(
        destination_files - source_files,
        key=lambda item: len(PurePosixPath(item).parts),
        reverse=True,
    ):
        destination = output / PurePosixPath(relative)
        if destination.is_symlink() or not destination.is_file():
            raise ValueError(f"refusing unsafe stale output: {destination}")
        destination.unlink()
        removed += 1
    for directory in sorted(
        (path for path in output.rglob("*") if path.is_dir()),
        key=lambda path: len(path.parts),
        reverse=True,
    ):
        try:
            directory.rmdir()
        except OSError:
            pass
    return copied, removed


def write_root_sitemap(output: Path, documentation_url: str) -> Path:
    """Write the Pages repository sitemap from the current public HTML files."""

    pages_root = output.parent.resolve()
    if (
        output.resolve().parent != pages_root
        or output.name != "ProCGroups_pages"
        or pages_root.name != "n-yamaguchi-0729.github.io"
        or pages_root.is_symlink()
    ):
        raise ValueError(f"refusing unexpected Pages repository: {pages_root}")

    suffix = "ProCGroups_pages/"
    if not documentation_url.endswith(suffix):
        raise ValueError(f"unexpected documentation URL: {documentation_url}")
    public_root = documentation_url[: -len(suffix)]

    public_files = [
        path
        for path in (
            pages_root / "index.html",
            pages_root / "homepage-en.html",
            pages_root / "homepage-jp.html",
        )
        if path.is_file() and not path.is_symlink()
    ]
    public_files.extend(
        path
        for path in output.rglob("*.html")
        if path.is_file() and not path.is_symlink()
    )

    urls: list[str] = []
    for path in sorted(public_files):
        relative = path.relative_to(pages_root).as_posix()
        if relative == "index.html":
            relative = ""
        elif relative.endswith("/index.html"):
            relative = relative[: -len("index.html")]
        urls.append(public_root + quote(relative, safe="/"))

    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ]
    for url in urls:
        lines.extend(("  <url>", f"    <loc>{escape(url)}</loc>", "  </url>"))
    lines.append("</urlset>")
    sitemap = pages_root / "sitemap.xml"
    content = "\n".join(lines) + "\n"
    if not sitemap.is_file() or sitemap.read_text(encoding="utf-8") != content:
        sitemap.write_text(content, encoding="utf-8", newline="\n")
    return sitemap


def main() -> int:
    config = load_config()
    source_root = resolve_config_path(config["source_root"])
    output = resolve_config_path(config["output_root"])
    modules = collect_procgroups_modules(
        source_root,
        config["expected_module_count"],
    )
    library_metadata = [{
        "id": COMPONENT,
        "display_name": config["library_name"],
        "import": config["root_import"],
        "module_roots": [COMPONENT],
        "module_count": len(modules),
    }]

    with tempfile.TemporaryDirectory(prefix="procgroups-pages-") as temp:
        staging = Path(temp) / "site"
        build_site.generate_site(
            lean_root=source_root,
            source_root=source_root,
            out=staging,
            title=config["title"],
            github_repo=config["source_repository"],
            commit=config["source_commit"],
            version=config["version"],
            source_ref=config["source_commit"],
            assets_root=ROOT / "assets",
            generated_at=config["generated_at"],
            documentation_url=config["documentation_url"],
            module_components=modules,
            component_display_names={COMPONENT: config["library_name"]},
            library_metadata=library_metadata,
            download_mode=build_site.DOWNLOAD_MODE_NONE,
            include_maintenance_files=False,
            reporter=build_site.BuildReporter(),
        )
        decorate_site(staging, config)
        write_manifest(staging, config["generated_at"])
        validate_site(staging, config, modules)
        copied, removed = synchronize_exact(staging, output)

    validate_site(output, config, modules)
    sitemap = write_root_sitemap(output, config["documentation_url"])
    print(
        f"ProCGroups pages are current: {len(modules)} modules, "
        f"{len(inventory_files(output))} files "
        f"({copied} copied, {removed} removed)"
    )
    print(f"Open locally: {output / 'index.html'}")
    print(f"Root sitemap: {sitemap}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
