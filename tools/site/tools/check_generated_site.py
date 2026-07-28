#!/usr/bin/env python3
"""Validate generated documentation policy, source permalinks, and build metadata."""

from __future__ import annotations

import argparse
from collections import Counter
from html import unescape
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import sys
from typing import NamedTuple
from urllib.parse import unquote, urlsplit

try:
    from public_paths import module_html_path, source_html_path
except ModuleNotFoundError:
    generator_root = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(generator_root))
    from public_paths import module_html_path, source_html_path


FULL_SHA = r"[0-9a-f]{40}"
SITE_MANIFEST_NAME = ".site-manifest.json"
SOURCE_LINK = re.compile(
    rf'https://github\.com/(?P<owner>[^/"\s]+)/(?P<repo>[^/"\s]+)/blob/'
    rf'(?P<sha>{FULL_SHA})/(?P<path>Lean4/[^"#\s]+\.lean)(?:#L\d+)?'
)
ANY_BLOB_LINK = re.compile(
    r"https://github\.com/[^/\"'\s<>()[\]{},;]+/[^/\"'\s<>()[\]{},;]+/blob/[^\"'\s<>()[\]{},;]+"
)
FORBIDDEN = (
    "proof-label",
    "proof-text",
    "No prose proof has been entered",
    ">Show proof<",
    "proof-pair",
    "PUBLIC_PAGE_SNAPSHOT",
)
TEXT_ASSET_SUFFIXES = frozenset(
    {".css", ".html", ".js", ".json", ".lean", ".md", ".py", ".toml", ".txt", ".xml", ".yaml", ".yml"}
)
TEXT_ASSET_NAMES = frozenset({".gitattributes", ".gitignore", ".nojekyll"})
SELF_CHECKER_PATH = "tools/check_generated_site.py"
HREF = re.compile(r'\bhref="([^"]+)"')
ID_ATTR = re.compile(r'\bid="([^"]+)"')
SOURCE_LINE = re.compile(
    r'class="[^"]*\bsrc-line\b[^"]*"\s+id="L(\d+)"'
)
DECL_REF = re.compile(
    r'<a\s+class="decl-ref"\s+href="[^"]+">([^<]+)</a>'
)
SCRIPT_BLOCK = re.compile(r"<script\b[\s\S]*?</script>", re.IGNORECASE)
HEADING_BLOCK = re.compile(
    r"<h[1-6]\b[^>]*>([\s\S]*?)</h[1-6]>",
    re.IGNORECASE,
)
HTML_TAG = re.compile(r"<[^>]+>")
SEARCH_INDEX_PATH = "assets/search-index.js"
TREE_DATA_PATH = "assets/tree-data.js"
LEGACY_LIBRARY_ABBREVIATION = re.compile(
    r"(?<![A-Za-z0-9])(?:PCG|LCFT|CES)(?![A-Za-z0-9])",
    re.IGNORECASE,
)
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
PUBLIC_ROOT_FILES = frozenset({"index.html", "build-info.json"})
PUBLIC_ASSET_FILES = frozenset({
    "assets/search-index.js",
    "assets/site.css",
    "assets/site.js",
    "assets/tree-data.js",
})
PUBLIC_FIND_FILES = frozenset({"find/index.html"})


class LibraryMetadata(NamedTuple):
    """The public library contract embedded in ``build-info.json``."""

    id: str
    display_name: str
    import_name: str
    module_roots: tuple[str, ...]
    module_count: int


class GeneratedData(NamedTuple):
    """Cross-indexed module and library facts derived from generated data."""

    library_ids: tuple[str, ...]
    library_names: tuple[str, ...]
    module_names: dict[str, str]
    module_libraries: dict[str, str]
    search_fragments: tuple[tuple[str, str, str], ...]


def inventory_tree(root: Path) -> tuple[list[str], set[str]]:
    """Return safety errors and regular files without following filesystem links."""
    errors: list[str] = []
    files: set[str] = set()
    if root.is_symlink():
        return [f"{root}: generated root must not be a symlink"], files
    if not root.exists():
        return [f"{root}: generated root does not exist"], files
    if not root.is_dir():
        return [f"{root}: generated root is not a directory"], files

    casefolded: dict[str, str] = {}
    pending: list[tuple[Path, PurePosixPath]] = [(root, PurePosixPath())]
    while pending:
        directory, relative_directory = pending.pop()
        try:
            entries = sorted(os.scandir(directory), key=lambda entry: entry.name)
        except OSError as error:
            errors.append(f"{directory}: cannot inspect generated tree: {error}")
            continue
        for entry in entries:
            relative = (relative_directory / entry.name).as_posix()
            folded = relative.casefold()
            previous = casefolded.setdefault(folded, relative)
            if previous != relative:
                errors.append(
                    f"{root}: case-insensitive path collision: {previous!r} and {relative!r}"
                )
            try:
                if entry.is_symlink():
                    errors.append(f"{relative}: generated tree must not contain symlinks")
                elif entry.is_dir(follow_symlinks=False):
                    pending.append((Path(entry.path), relative_directory / entry.name))
                elif entry.is_file(follow_symlinks=False):
                    files.add(relative)
                else:
                    errors.append(f"{relative}: unsupported non-file entry in generated tree")
            except OSError as error:
                errors.append(f"{relative}: cannot inspect generated tree entry: {error}")
    return errors, files


def check_public_artifacts(root: Path) -> list[str]:
    """Reject files that do not belong in the deployed documentation portal."""
    inventory_errors, files = inventory_tree(root)
    if inventory_errors:
        return inventory_errors
    errors: list[str] = []
    allowed_fixed = PUBLIC_ROOT_FILES | PUBLIC_ASSET_FILES | PUBLIC_FIND_FILES
    for relative in sorted(files):
        path = PurePosixPath(relative)
        is_library_page = (
            len(path.parts) >= 3
            and path.parts[0] == "library"
            and path.suffix.casefold() == ".html"
        )
        if relative in allowed_fixed or is_library_page:
            continue
        errors.append(
            f"{relative}: file is not part of the public documentation allowlist"
        )
    return errors


def valid_manifest_path(value: str) -> bool:
    if not value or "\\" in value:
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and path.as_posix() == value and all(
        part not in {"", ".", ".."} for part in path.parts
    )


def check_manifest(root: Path, actual_files: set[str]) -> list[str]:
    errors: list[str] = []
    manifest_path = root / SITE_MANIFEST_NAME
    if SITE_MANIFEST_NAME not in actual_files:
        # Public deployments intentionally omit generator-maintenance files.
        # When a private staging manifest is present it remains a strict,
        # exhaustive contract; its absence is valid for the deployed tree.
        return errors
    try:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        return [f"{SITE_MANIFEST_NAME}: invalid manifest: {error}"]
    if not isinstance(data, dict):
        return [f"{SITE_MANIFEST_NAME}: manifest root must be an object"]

    raw_files = data.get("files")
    if not isinstance(raw_files, list):
        return [f"{SITE_MANIFEST_NAME}: files must be an array"]
    manifest_files: set[str] = set()
    for index, value in enumerate(raw_files):
        if not isinstance(value, str) or not valid_manifest_path(value):
            errors.append(
                f"{SITE_MANIFEST_NAME}: files[{index}] is not a normalized relative POSIX path: {value!r}"
            )
            continue
        if value in manifest_files:
            errors.append(f"{SITE_MANIFEST_NAME}: duplicate file entry: {value!r}")
        manifest_files.add(value)

    file_count = data.get("file_count")
    if isinstance(file_count, bool) or not isinstance(file_count, int):
        errors.append(f"{SITE_MANIFEST_NAME}: file_count must be an integer")
    elif file_count != len(raw_files):
        errors.append(
            f"{SITE_MANIFEST_NAME}: file_count {file_count} does not equal files length {len(raw_files)}"
        )
    if SITE_MANIFEST_NAME not in manifest_files:
        errors.append(f"{SITE_MANIFEST_NAME}: manifest must list itself")

    missing = sorted(manifest_files - actual_files)
    extra = sorted(actual_files - manifest_files)
    if missing:
        errors.append(
            f"{SITE_MANIFEST_NAME}: listed files missing from generated tree: {', '.join(missing[:20])}"
        )
    if extra:
        errors.append(
            f"{SITE_MANIFEST_NAME}: generated tree has unlisted files: {', '.join(extra[:20])}"
        )
    return errors


def is_text_asset(relative: str) -> bool:
    path = PurePosixPath(relative)
    return path.name.casefold() in TEXT_ASSET_NAMES or path.suffix.casefold() in TEXT_ASSET_SUFFIXES


def local_link_target(relative: str, raw_href: str) -> str | None:
    href = unescape(raw_href.strip())
    if not href or href.startswith("#"):
        return None
    parsed = urlsplit(href)
    if parsed.scheme or parsed.netloc:
        return None
    link_path = unquote(parsed.path)
    if not link_path:
        return None
    if link_path.startswith("/"):
        target = posixpath.normpath(link_path.lstrip("/"))
    else:
        target = posixpath.normpath(
            posixpath.join(posixpath.dirname(relative), link_path)
        )
    if target in {"", "."}:
        target = "index.html"
    elif link_path.endswith("/"):
        target = posixpath.join(target, "index.html")
    return target


def module_source_path(module_name: str) -> str:
    """Return the repository path for a Lean module in the shared source root."""
    return f"Lean4/{module_name.replace('.', '/')}.lean"


def source_page_for_module(module_name: str, library_id: str) -> str:
    """Return the canonical rendered-source URL for a public Lean module."""
    return source_html_path(
        module_name.replace(".", "/") + ".lean",
        library_id,
    )


def public_library_directories(root: Path) -> set[str]:
    library_root = root / "library"
    if not library_root.is_dir() or library_root.is_symlink():
        return set()
    try:
        return {
            entry.name
            for entry in os.scandir(library_root)
            if entry.is_dir(follow_symlinks=False) and not entry.is_symlink()
        }
    except OSError:
        return set()


def contains_legacy_library_abbreviation(value: str) -> bool:
    return LEGACY_LIBRARY_ABBREVIATION.search(unquote(value)) is not None


def parse_library_metadata(
    build_info: object,
    errors: list[str],
) -> tuple[LibraryMetadata, ...] | None:
    """Parse the optional data-driven public-library contract.

    Older generated sites did not publish this array, so its absence is a
    supported fallback.  If the key is present, however, every field is
    validated and the metadata becomes authoritative.
    """
    if not isinstance(build_info, dict) or "libraries" not in build_info:
        return None
    raw_libraries = build_info.get("libraries")
    if not isinstance(raw_libraries, list) or not raw_libraries:
        errors.append("build-info.json: libraries must be a nonempty array")
        return ()

    libraries: list[LibraryMetadata] = []
    seen_ids: set[str] = set()
    seen_names: set[str] = set()
    seen_roots: set[str] = set()
    for index, raw in enumerate(raw_libraries):
        label = f"build-info.json: libraries[{index}]"
        if not isinstance(raw, dict):
            errors.append(f"{label} must be an object")
            continue
        library_id = raw.get("id")
        display_name = raw.get("display_name")
        import_name = raw.get("import")
        raw_roots = raw.get("module_roots")
        module_count = raw.get("module_count")
        if (
            not isinstance(library_id, str)
            or not library_id
            or not valid_manifest_path(library_id)
            or len(PurePosixPath(library_id).parts) != 1
            or library_id == "src"
        ):
            errors.append(f"{label}.id must be one safe directory name")
            continue
        if not isinstance(display_name, str) or not display_name.strip():
            errors.append(f"{label}.display_name must be nonempty")
            continue
        if not isinstance(import_name, str) or not MODULE_NAME.fullmatch(import_name):
            errors.append(f"{label}.import must be a Lean module name")
            continue
        if (
            not isinstance(raw_roots, list)
            or not raw_roots
            or any(
                not isinstance(root, str)
                or not MODULE_NAME.fullmatch(root)
                or "." in root
                for root in raw_roots
            )
        ):
            errors.append(
                f"{label}.module_roots must be a nonempty array of top-level module names"
            )
            continue
        roots = tuple(raw_roots)
        if len(set(roots)) != len(roots):
            errors.append(f"{label}.module_roots contains duplicates")
            continue
        if (
            isinstance(module_count, bool)
            or not isinstance(module_count, int)
            or module_count < 0
        ):
            errors.append(f"{label}.module_count must be a nonnegative integer")
            continue
        if library_id in seen_ids:
            errors.append(f"build-info.json: duplicate library id {library_id!r}")
        if display_name in seen_names:
            errors.append(
                f"build-info.json: duplicate library display_name {display_name!r}"
            )
        overlap = seen_roots.intersection(roots)
        if overlap:
            errors.append(
                "build-info.json: module roots belong to more than one library: "
                + ", ".join(sorted(overlap))
            )
        if contains_legacy_library_abbreviation(library_id):
            errors.append(
                f"build-info.json: public library id uses a legacy abbreviation: {library_id!r}"
            )
        if contains_legacy_library_abbreviation(display_name):
            errors.append(
                "build-info.json: public library display_name uses a legacy "
                f"abbreviation: {display_name!r}"
            )
        seen_ids.add(library_id)
        seen_names.add(display_name)
        seen_roots.update(roots)
        libraries.append(
            LibraryMetadata(
                id=library_id,
                display_name=display_name,
                import_name=import_name,
                module_roots=roots,
                module_count=module_count,
            )
        )
    return tuple(libraries)


def load_javascript_json(
    root: Path,
    relative: str,
    assignment: str,
    errors: list[str],
) -> object | None:
    path = root / relative
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        errors.append(f"{relative}: cannot read generated JavaScript data: {error}")
        return None
    if not text.startswith(assignment):
        errors.append(f"{relative}: expected assignment prefix {assignment!r}")
        return None
    payload = text[len(assignment) :].strip()
    if not payload.endswith(";"):
        errors.append(f"{relative}: generated assignment must end with a semicolon")
        return None
    try:
        return json.loads(payload[:-1])
    except json.JSONDecodeError as error:
        errors.append(f"{relative}: invalid generated JSON payload: {error}")
        return None


def root_relative_target(raw_url: str) -> tuple[str | None, str]:
    parsed = urlsplit(unescape(str(raw_url).strip()))
    if parsed.scheme or parsed.netloc:
        return None, ""
    path = unquote(parsed.path)
    target = posixpath.normpath(path) if path else "index.html"
    if path.endswith("/"):
        target = posixpath.join(target, "index.html")
    return target, unquote(parsed.fragment)


def validate_generated_data(
    root: Path,
    actual_files: set[str],
    libraries: tuple[LibraryMetadata, ...] | None,
    errors: list[str],
) -> GeneratedData:
    metadata_by_id = {library.id: library for library in libraries or ()}
    metadata_by_name = {
        library.display_name: library for library in libraries or ()
    }

    tree = load_javascript_json(
        root,
        TREE_DATA_PATH,
        "window.LEAN_DOCS_TREE=",
        errors,
    )
    tree_urls: list[str] = []
    module_names: dict[str, str] = {}
    module_libraries: dict[str, str] = {}
    root_names: list[str] = []
    inferred_root_ids: dict[str, str] = {}

    def walk(nodes: object, root_name: str, expected_id: str | None) -> set[str]:
        root_ids: set[str] = set()
        if not isinstance(nodes, list):
            errors.append(f"{TREE_DATA_PATH}: tree children must be arrays")
            return root_ids
        for node in nodes:
            if not isinstance(node, dict):
                errors.append(f"{TREE_DATA_PATH}: tree node is not an object")
                continue
            if "u" in node:
                url = str(node.get("u", ""))
                module_name = str(node.get("m", ""))
                tree_urls.append(url)
                target, fragment = root_relative_target(url)
                if fragment:
                    errors.append(
                        f"{TREE_DATA_PATH}: module tree URL must not use a fragment: {url}"
                    )
                if target is None:
                    errors.append(
                        f"{TREE_DATA_PATH}: module tree URL must be local: {url}"
                    )
                    continue
                if target not in actual_files:
                    errors.append(
                        f"{TREE_DATA_PATH}: missing tree target {url!r} -> {target!r}"
                    )
                target_path = PurePosixPath(target)
                if (
                    len(target_path.parts) < 3
                    or target_path.parts[0] != "library"
                    or target_path.suffix != ".html"
                    or "src" in target_path.parts[2:]
                ):
                    errors.append(
                        f"{TREE_DATA_PATH}: module URL is outside a public library: {url!r}"
                    )
                    continue
                library_id = target_path.parts[1]
                root_ids.add(library_id)
                if expected_id is not None and library_id != expected_id:
                    errors.append(
                        f"{TREE_DATA_PATH}: root {root_name!r} contains module URL "
                        f"for {library_id!r}, expected {expected_id!r}"
                    )
                if not MODULE_NAME.fullmatch(module_name):
                    errors.append(
                        f"{TREE_DATA_PATH}: module node {url!r} has invalid m={module_name!r}"
                    )
                    continue
                expected_target = module_html_path(module_name, library_id)
                if target != expected_target:
                    errors.append(
                        f"{TREE_DATA_PATH}: module {module_name!r} uses URL {target!r}, "
                        f"expected {expected_target!r}"
                    )
                if target in module_names:
                    errors.append(f"{TREE_DATA_PATH}: duplicate module URL {target!r}")
                elif module_name in module_names.values():
                    errors.append(
                        f"{TREE_DATA_PATH}: duplicate Lean module name {module_name!r}"
                    )
                module_names[target] = module_name
                module_libraries[target] = library_id
                metadata = metadata_by_id.get(library_id)
                if metadata is not None:
                    module_root = module_name.split(".", 1)[0]
                    if module_root not in metadata.module_roots:
                        errors.append(
                            f"{TREE_DATA_PATH}: module {module_name!r} is not owned by "
                            f"library {library_id!r}"
                        )
            if "c" in node:
                root_ids.update(walk(node["c"], root_name, expected_id))
        return root_ids

    if isinstance(tree, list):
        for root_index, node in enumerate(tree):
            if not isinstance(node, dict):
                errors.append(
                    f"{TREE_DATA_PATH}: tree root {root_index} is not an object"
                )
                continue
            root_name = str(node.get("n", ""))
            root_names.append(root_name)
            metadata = metadata_by_name.get(root_name)
            expected_id = metadata.id if metadata is not None else None
            if libraries is not None and metadata is None:
                errors.append(
                    f"{TREE_DATA_PATH}: unexpected library root name {root_name!r}"
                )
            root_ids = walk(node.get("c", []), root_name, expected_id)
            if len(root_ids) == 1:
                inferred_root_ids[root_name] = next(iter(root_ids))
            elif len(root_ids) > 1:
                errors.append(
                    f"{TREE_DATA_PATH}: root {root_name!r} mixes library directories "
                    f"{sorted(root_ids)}"
                )
            elif metadata is not None and metadata.module_count:
                errors.append(
                    f"{TREE_DATA_PATH}: root {root_name!r} contains no module URLs"
                )
    elif tree is not None:
        errors.append(f"{TREE_DATA_PATH}: payload must be an array")

    if len(tree_urls) != len(set(tree_urls)):
        errors.append(f"{TREE_DATA_PATH}: duplicate module URL")

    actual_library_ids = public_library_directories(root)
    if libraries is not None:
        expected_library_ids = {library.id for library in libraries}
        expected_library_names = {library.display_name for library in libraries}
        if actual_library_ids != expected_library_ids:
            errors.append(
                "library/: directory set does not match build-info.json; "
                f"expected={sorted(expected_library_ids)}, "
                f"found={sorted(actual_library_ids)}"
            )
        if len(root_names) != len(expected_library_names) or set(root_names) != expected_library_names:
            errors.append(
                f"{TREE_DATA_PATH}: library roots do not match build-info.json; "
                f"expected={sorted(expected_library_names)}, found={root_names}"
            )
    else:
        expected_library_ids = actual_library_ids
        expected_library_names = set(root_names)
        inferred_ids = set(inferred_root_ids.values())
        if inferred_ids != actual_library_ids:
            errors.append(
                f"{TREE_DATA_PATH}: library roots do not cover library/ directories; "
                f"tree={sorted(inferred_ids)}, directories={sorted(actual_library_ids)}"
            )

    actual_module_pages = {
        relative
        for relative in actual_files
        if (
            len(PurePosixPath(relative).parts) >= 3
            and PurePosixPath(relative).parts[0] == "library"
            and PurePosixPath(relative).parts[1] in expected_library_ids
            and "src" not in PurePosixPath(relative).parts[2:]
            and PurePosixPath(relative).suffix == ".html"
        )
    }
    tree_module_pages = set(module_names)
    if tree_module_pages != actual_module_pages:
        missing = sorted(actual_module_pages - tree_module_pages)
        extra = sorted(tree_module_pages - actual_module_pages)
        errors.append(
            f"{TREE_DATA_PATH}: module coverage mismatch; "
            f"missing={missing[:10]}, extra={extra[:10]}"
        )

    expected_source_pages = {
        source_page_for_module(module_names[relative], module_libraries[relative])
        for relative in tree_module_pages
    }
    actual_source_pages = {
        relative
        for relative in actual_files
        if (
            len(PurePosixPath(relative).parts) >= 4
            and PurePosixPath(relative).parts[0] == "library"
            and PurePosixPath(relative).parts[1] in expected_library_ids
            and PurePosixPath(relative).parts[2] == "src"
            and PurePosixPath(relative).suffix == ".html"
        )
    }
    if actual_source_pages != expected_source_pages:
        missing = sorted(expected_source_pages - actual_source_pages)
        extra = sorted(actual_source_pages - expected_source_pages)
        errors.append(
            "rendered source-page coverage mismatch; "
            f"missing={missing[:10]}, extra={extra[:10]}"
        )

    if libraries is not None:
        module_counts = Counter(module_libraries.values())
        module_name_set = set(module_names.values())
        for library in libraries:
            found = module_counts[library.id]
            if found != library.module_count:
                errors.append(
                    f"build-info.json: library {library.id!r} declares "
                    f"module_count={library.module_count}, tree contains {found}"
                )
            if library.import_name not in module_name_set:
                errors.append(
                    f"build-info.json: library import {library.import_name!r} "
                    "has no generated module page"
                )
            if library.import_name.split(".", 1)[0] not in library.module_roots:
                errors.append(
                    f"build-info.json: import {library.import_name!r} is outside "
                    f"module_roots for {library.id!r}"
                )

    search = load_javascript_json(
        root,
        SEARCH_INDEX_PATH,
        "window.LEAN_DOCS_INDEX=",
        errors,
    )
    search_fragments: list[tuple[str, str, str]] = []
    if isinstance(search, list):
        urls: set[str] = set()
        library_names: list[str] = []
        search_modules: dict[str, str] = {}
        for index, entry in enumerate(search):
            if not isinstance(entry, dict):
                errors.append(f"{SEARCH_INDEX_PATH}: entry {index} is not an object")
                continue
            name = str(entry.get("n", ""))
            url = str(entry.get("u", ""))
            if not name or not url:
                errors.append(
                    f"{SEARCH_INDEX_PATH}: entry {index} requires nonempty n and u"
                )
                continue
            if "anonymous_" in name:
                errors.append(
                    f"{SEARCH_INDEX_PATH}: synthetic anonymous declaration leaked: {name}"
                )
            if url in urls:
                errors.append(f"{SEARCH_INDEX_PATH}: duplicate URL: {url}")
            urls.add(url)
            if entry.get("k") == "Library":
                library_names.append(name)
                if contains_legacy_library_abbreviation(name):
                    errors.append(
                        f"{SEARCH_INDEX_PATH}: library name uses a legacy "
                        f"abbreviation: {name!r}"
                    )
            elif entry.get("k") == "Lean file":
                search_modules[url] = name
            target, fragment = root_relative_target(url)
            if target is None:
                errors.append(
                    f"{SEARCH_INDEX_PATH}: external search target is forbidden: {url}"
                )
            elif target not in actual_files:
                errors.append(
                    f"{SEARCH_INDEX_PATH}: missing search target {url!r} -> {target!r}"
                )
            elif fragment:
                search_fragments.append((target, fragment, url))
        if (
            len(library_names) != len(expected_library_names)
            or set(library_names) != expected_library_names
        ):
            errors.append(
                f"{SEARCH_INDEX_PATH}: Library entries do not match generated "
                f"libraries; expected={sorted(expected_library_names)}, "
                f"found={library_names}"
            )
        if set(search_modules) != tree_module_pages:
            missing = sorted(tree_module_pages - set(search_modules))
            extra = sorted(set(search_modules) - tree_module_pages)
            errors.append(
                f"{SEARCH_INDEX_PATH}: Lean file coverage does not match the tree; "
                f"missing={missing[:10]}, extra={extra[:10]}"
            )
        for url, name in search_modules.items():
            if url in module_names and name != module_names[url]:
                errors.append(
                    f"{SEARCH_INDEX_PATH}: module {url!r} is named {name!r}, "
                    f"tree uses {module_names[url]!r}"
                )
    elif search is not None:
        errors.append(f"{SEARCH_INDEX_PATH}: payload must be an array")

    return GeneratedData(
        library_ids=tuple(
            library.id for library in libraries
        )
        if libraries is not None
        else tuple(sorted(expected_library_ids)),
        library_names=tuple(
            library.display_name for library in libraries
        )
        if libraries is not None
        else tuple(root_names),
        module_names=module_names,
        module_libraries=module_libraries,
        search_fragments=tuple(search_fragments),
    )


def check_root(root: Path) -> list[str]:
    errors, actual_files = inventory_tree(root)
    if errors:
        return errors
    errors.extend(check_manifest(root, actual_files))
    if any(relative.startswith("download/") for relative in actual_files):
        errors.append("download/: generated download pages and archives are forbidden")
    for relative in sorted(actual_files):
        if contains_legacy_library_abbreviation(relative):
            errors.append(
                f"{relative}: public path uses a legacy library abbreviation"
            )

    build_info_path = root / "build-info.json"
    try:
        build_info = json.loads(build_info_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        errors.append(f"{build_info_path}: invalid build metadata: {error}")
        build_info = {}
    if not isinstance(build_info, dict):
        errors.append("build-info.json: metadata root must be an object")
        build_info = {}
    libraries = parse_library_metadata(build_info, errors)
    generated = validate_generated_data(root, actual_files, libraries, errors)
    module_pages = set(generated.module_names)
    source_pages = {
        source_page_for_module(
            generated.module_names[relative],
            generated.module_libraries[relative],
        )
        for relative in module_pages
    }

    html_files = sorted(relative for relative in actual_files if relative.endswith(".html"))
    valid_source_links = 0
    source_shas: set[str] = set()
    source_repositories: set[str] = set()
    html_ids: dict[str, set[str]] = {}
    fragment_links: list[tuple[str, str, str, str]] = []

    for relative in sorted(actual_files):
        if not is_text_asset(relative):
            continue
        path = root / PurePosixPath(relative)
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            errors.append(f"{relative}: invalid UTF-8 generated text asset: {error}")
            continue
        if relative.endswith(".html"):
            ids = [unescape(value) for value in ID_ATTR.findall(text)]
            duplicate_ids = sorted(
                value for value, count in Counter(ids).items() if count > 1
            )
            if duplicate_ids:
                errors.append(
                    f"{relative}: duplicate HTML ids: {duplicate_ids[:20]}"
                )
            html_ids[relative] = set(ids)
            for heading in HEADING_BLOCK.findall(SCRIPT_BLOCK.sub("", text)):
                visible_heading = unescape(HTML_TAG.sub(" ", heading))
                if contains_legacy_library_abbreviation(visible_heading):
                    errors.append(
                        f"{relative}: page heading uses a legacy library abbreviation: "
                        f"{visible_heading.strip()!r}"
                    )

            if "No prose statement has been entered." in text:
                errors.append(f"{relative}: missing-prose placeholder must not be public")
            for bad_grammar in (
                "1 files",
                "1 declarations",
                "1 sections",
                "1 top-level groups",
            ):
                if re.search(
                    rf"(?<![0-9]){re.escape(bad_grammar)}(?![A-Za-z0-9])",
                    text,
                ):
                    errors.append(
                        f"{relative}: incorrect singular grammar {bad_grammar!r}"
                    )
            for label in DECL_REF.findall(text):
                if "." not in unescape(label):
                    errors.append(
                        f"{relative}: unsafe short-name declaration link: {unescape(label)!r}"
                    )
            if relative in module_pages:
                without_scripts = SCRIPT_BLOCK.sub("", text)
                if (
                    (r"\(" in without_scripts or r"\[" in without_scripts)
                    and "mathjax@3.2.2" not in text
                ):
                    errors.append(
                        f"{relative}: TeX prose is present without the pinned MathJax renderer"
                    )

            if relative in source_pages:
                source_lines = [int(value) for value in SOURCE_LINE.findall(text)]
                if source_lines != list(range(1, len(source_lines) + 1)):
                    errors.append(
                        f"{relative}: source line ids are not the contiguous L1..Ln sequence"
                    )

            for href in HREF.findall(text):
                target = local_link_target(relative, href)
                parsed_href = urlsplit(unescape(href.strip()))
                if (
                    not parsed_href.scheme
                    and not parsed_href.netloc
                    and parsed_href.fragment
                ):
                    fragment_target = target or relative
                    fragment_links.append(
                        (
                            relative,
                            href,
                            fragment_target,
                            unquote(parsed_href.fragment),
                        )
                    )
                if target is None:
                    continue
                if target == ".." or target.startswith("../"):
                    errors.append(
                        f"{relative}: local link escapes the generated site: {href}"
                    )
                elif target not in actual_files:
                    errors.append(
                        f"{relative}: broken local link {href!r} -> {target!r}"
                    )
        # The distributed checker necessarily names the markers it enforces.
        if relative != SELF_CHECKER_PATH:
            for marker in FORBIDDEN:
                if marker in text:
                    errors.append(f"{relative}: forbidden generated-proof marker {marker!r}")
        valid = list(SOURCE_LINK.finditer(text))
        valid_source_links += len(valid)
        source_shas.update(match.group("sha") for match in valid)
        source_repositories.update(
            f"https://github.com/{match.group('owner')}/{match.group('repo')}"
            for match in valid
        )
        for match in ANY_BLOB_LINK.finditer(text):
            if not SOURCE_LINK.fullmatch(match.group(0)):
                errors.append(f"{relative}: non-permalink or wrong source path: {match.group(0)}")

        module_name = generated.module_names.get(relative)
        expected_source = (
            module_source_path(module_name) if module_name is not None else None
        )
        if expected_source is not None and not any(
            match.group("path") == expected_source for match in valid
        ):
            errors.append(
                f"{relative}: library/module page lacks a SHA-pinned source permalink "
                f"for {expected_source!r}"
            )

    for source_relative, href, target, fragment in fragment_links:
        if target in html_ids and fragment not in html_ids[target]:
            errors.append(
                f"{source_relative}: broken local fragment {href!r} "
                f"-> {target!r}#{fragment}"
            )

    for target, fragment, url in generated.search_fragments:
        if target in html_ids and fragment not in html_ids[target]:
            errors.append(
                f"{SEARCH_INDEX_PATH}: missing search fragment {url!r}"
            )

    commit = str(build_info.get("commit", ""))
    source_ref = str(build_info.get("sourceRef", ""))
    source_repository = str(build_info.get("sourceRepository", "")).rstrip("/")
    if source_repository.endswith(".git"):
        source_repository = source_repository[:-4]
    if not re.fullmatch(FULL_SHA, commit):
        errors.append(f"build-info.json: commit is not a full SHA: {commit!r}")
    if source_ref != commit:
        errors.append(
            f"build-info.json: sourceRef {source_ref!r} does not equal commit {commit!r}"
        )
    if source_shas and source_shas != {commit}:
        errors.append(f"source links use SHAs {sorted(source_shas)}, expected only {commit}")
    if source_repositories and source_repositories != {source_repository}:
        errors.append(
            "source links use repositories "
            f"{sorted(source_repositories)}, expected only {source_repository!r}"
        )
    if not html_files:
        errors.append(f"{root}: no HTML files found")
    if valid_source_links == 0:
        errors.append(f"{root}: no SHA-pinned Lean source links found")

    print(
        f"{root}: {len(html_files)} HTML files, "
        f"{len(module_pages)} modules, "
        f"{valid_source_links} SHA-pinned Lean source links"
    )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()
    errors = [
        error
        for root in args.roots
        for error in (
            *check_root(root.absolute()),
            *check_public_artifacts(root.absolute()),
        )
    ]
    errors = list(dict.fromkeys(errors))
    if errors:
        for error in errors[:200]:
            print(f"ERROR: {error}", file=sys.stderr)
        if len(errors) > 200:
            print(f"ERROR: ... and {len(errors) - 200} more", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
