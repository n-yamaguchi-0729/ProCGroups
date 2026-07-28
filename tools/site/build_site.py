from __future__ import annotations

import atexit
import argparse
import html
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import io
import zipfile
from datetime import datetime, timezone
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Any, Iterable

from public_paths import module_html_path, source_html_path

sys.dont_write_bytecode = True

DECL_KINDS = (
    "def", "theorem", "lemma", "instance", "structure", "class", "inductive",
    "abbrev", "axiom", "opaque", "constant", "example", "macro"
)
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*(?P<kind>"
    + "|".join(DECL_KINDS)
    + r")\b(?P<rest>.*)$"
)
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$")
SECTION_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_'.]+))?\s*$"
)
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)")
AXIOM_COMMAND_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*"
    r"axiom\s+([^\s(:]+)"
)
TOPLEVEL_BOUNDARY_RE = re.compile(
    r"^\s*(?:"
    r"(?:noncomputable\s+)?section\b|"
    r"variables?\b|universes?\b|"
    r"attribute\b|open\b|export\b|include\b|omit\b|"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*local\b|"
    r"set_option\b|"
    r"scoped(?:\[[^\]\n]+\])?\s+"
    r"(?:notation|infix|prefix|postfix|macro|syntax)\b|"
    r"(?:notation|infix[lr]?|prefix|postfix|syntax|elab|command_elab|"
    r"initialize|builtin_initialize)\b|"
    r"\#[A-Za-z_][A-Za-z0-9_]*\b"
    r")"
)
DECLARATION_WRAPPER_START_RE = re.compile(
    r"^\s*(?:omit|include|set_option|open|export|attribute|local)\b"
)
IDENT_RE = re.compile(r"^\s*(`[^`]+`|[^\s\[\]\{\}\(\):=]+)")
TOKEN_RE = re.compile(r"[^\W\d][\w'.₀₁₂₃₄₅₆₇₈₉]*|_[\w'.₀₁₂₃₄₅₆₇₈₉]*", re.UNICODE)

SORRY_TOKEN_RE = re.compile(r"\b(?:sorry|admit)\b")

KEYWORDS = {
    "import", "namespace", "end", "section", "variable", "variables", "open", "where",
    "def", "theorem", "lemma", "example", "instance", "structure", "class", "inductive",
    "abbrev", "axiom", "opaque", "constant", "noncomputable", "private", "protected",
    "partial", "unsafe", "scoped", "by", "match", "with", "fun", "let", "in", "if",
    "then", "else", "do", "return", "have", "show", "calc", "Type", "Prop", "extends",
    "deriving", "forall", "Forall", "exists", "simp", "rw", "exact", "apply", "intro",
    "intros", "constructor", "cases", "induction", "rfl"
}

KIND_LABELS = {
    "theorem": "Theorem",
    "lemma": "Lemma",
    "def": "Definition",
    "abbrev": "Abbreviation",
    "instance": "Instance",
    "structure": "Structure",
    "class": "Class",
    "inductive": "Inductive",
    "axiom": "Axiom",
    "opaque": "opaque",
    "constant": "Constant",
    "example": "Example",
    "macro": "Macro",
}
KIND_PLURAL_LABELS = {
    "theorem": "Theorems",
    "lemma": "Lemmas",
    "def": "Definitions",
    "abbrev": "Abbreviations",
    "instance": "Instances",
    "structure": "Structures",
    "class": "Classes",
    "inductive": "Inductive types",
    "axiom": "Axioms",
    "opaque": "Opaque declarations",
    "constant": "Constants",
    "example": "Examples",
    "macro": "Macros",
}
PROOF_KINDS = {"theorem", "lemma", "example"}
SKIP_LEAN_DIRS = {".lake", "public", "docs", "dist", "build", "site_history", "_site"}
SKIP_LEAN_FILES = {"lakefile.lean"}
DEFAULT_ASSET_ROOT = Path(__file__).resolve().parent / "assets"
SITE_MANIFEST_NAME = ".site-manifest.json"
DISTRIBUTION_MANIFEST_NAME = ".lean-distribution-manifest.json"
AXIOM_MANIFEST_NAME = "axiom-manifest.json"
REPOSITORY_METADATA_NAMES = frozenset({
    ".git",
    ".github",
    "license",
    "license.md",
    "copying",
    "changelog.md",
    "security.md",
    "contributing.md",
    "release.md",
    "code_of_conduct.md",
    "citation.cff",
})
DEFAULT_LEAN_PACKAGE_NAME = "ProCGroups"
DEFAULT_LEAN_ZIP_NAME = "lean-project.zip"
DEFAULT_LEAN_REPOSITORY_MIRROR = Path(__file__).resolve().parents[2] / "Lean4"
DEFAULT_PAGES_OUTPUT_ROOT = (
    Path(__file__).resolve().parents[3]
    / "n-yamaguchi-0729.github.io"
    / "ProCGroups_pages"
)
DEFAULT_PUBLIC_SITE_URL = "https://n-yamaguchi-0729.github.io/"
DEFAULT_DOCUMENTATION_URL = DEFAULT_PUBLIC_SITE_URL + "ProCGroups_pages/"
DOWNLOAD_MODE_DISTRIBUTION = "distribution"
DOWNLOAD_MODE_GITHUB_ARCHIVE = "github-archive"
DOWNLOAD_MODE_NONE = "none"
DOWNLOAD_MODES = frozenset({
    DOWNLOAD_MODE_DISTRIBUTION,
    DOWNLOAD_MODE_GITHUB_ARCHIVE,
    DOWNLOAD_MODE_NONE,
})
DOCUMENTATION_DESCRIPTION = (
    "Published Lean 4 libraries for formalized mathematics."
)
GOOGLE_TAG_ID = "G-NGQXB29549"
GOOGLE_TAG = f'''<!-- Google tag (gtag.js) -->
<script async src="https://www.googletagmanager.com/gtag/js?id={GOOGLE_TAG_ID}"></script>
<script>
  window.dataLayer = window.dataLayer || [];
  function gtag(){{dataLayer.push(arguments);}}
  gtag('js', new Date());

  gtag('config', '{GOOGLE_TAG_ID}');
</script>'''
MATHJAX_TAG = r'''<script>
window.MathJax = {
  tex: {
    inlineMath: [['\\(', '\\)']],
    displayMath: [['\\[', '\\]']]
  },
  options: {
    ignoreHtmlClass: 'tex2jax_ignore',
    processHtmlClass: 'tex2jax_process'
  }
};
</script>
<script defer src="https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-mml-chtml.js"></script>'''


class BuildReporter:
    def __init__(self, enabled: bool = True) -> None:
        self.enabled = enabled
        self.started = time.perf_counter()
        self.step_started = self.started
        self.current = ""

    def elapsed(self) -> float:
        return time.perf_counter() - self.started

    def log(self, message: str) -> None:
        if self.enabled:
            print(f"[{self.elapsed():7.1f}s] {message}", flush=True)

    def step(self, message: str) -> None:
        self.current = message
        self.step_started = time.perf_counter()
        self.log(f"START {message}")

    def done(self, message: str | None = None, extra: str = "") -> None:
        label = message or self.current
        duration = time.perf_counter() - self.step_started
        suffix = f" {extra}" if extra else ""
        self.log(f"DONE  {label} ({duration:.1f}s){suffix}")

    def progress(self, message: str) -> None:
        self.log(message)


@dataclass(slots=True)
class WriteStats:
    generated: int = 0
    written: int = 0
    unchanged: int = 0
    deleted: int = 0


def top_level_module_from_relative_path(rel: Path) -> str:
    if not rel.parts:
        return ""
    first = rel.parts[0]
    if len(rel.parts) == 1:
        top = Path(first).stem
    else:
        top = first
    if top.endswith("_terms"):
        top = top[: -len("_terms")]
    return top


def is_safe_lean_source_path(path: Path, root: Path) -> bool:
    try:
        rel = path.relative_to(root)
    except ValueError:
        return False
    if not rel.parts or any(part.startswith(".") for part in rel.parts):
        return False
    return rel.suffix == ".lean"


def source_inventory_errors(lean_root: Path) -> list[str]:
    errors: list[str] = []
    if lean_root.exists():
        for path in sorted(lean_root.rglob("*.lean")):
            rel = path.relative_to(lean_root)
            if rel.name in SKIP_LEAN_FILES:
                continue
            if any(part.startswith(".") or part in SKIP_LEAN_DIRS for part in rel.parts):
                continue
            if not is_safe_lean_source_path(path, lean_root):
                errors.append(f"invalid Lean file under data/lean4: {rel.as_posix()}")
    return errors


def assert_source_inventory(lean_root: Path) -> None:
    errors = source_inventory_errors(lean_root)
    if errors:
        details = "\n".join(f"- {item}" for item in errors[:50])
        if len(errors) > 50:
            details += f"\n- ... and {len(errors) - 50} more"
        raise SystemExit("Invalid Lean source paths were found.\n" + details)


def read_static_asset(name: str, assets_root: Path | None = None) -> str:
    """Read packaged CSS/JS assets used by generated pages."""
    candidates: list[Path] = []
    if assets_root is not None:
        candidates.append(assets_root / name)
    candidates.append(Path(__file__).resolve().parent / "data" / "assets" / name)
    candidates.append(DEFAULT_ASSET_ROOT / name)
    for path in candidates:
        if path.exists():
            return path.read_text(encoding="utf-8")
    raise FileNotFoundError(
        "Required asset was not found: "
        + ", ".join(str(path) for path in candidates)
    )


@dataclass(slots=True)
class Declaration:
    kind: str
    name: str
    full_name: str
    line: int
    code: str
    doc: str
    module: str
    rel_path: str
    id: str
    natural: dict[str, Any] = field(default_factory=dict)
    component: str = ""
    source_component_prefix: bool | None = None


@dataclass(slots=True)
class Module:
    name: str
    rel_path: str
    source: str
    imports: list[str]
    module_doc: str
    decls: list[Declaration]
    imported_by: list[str] = field(default_factory=list)
    natural: dict[str, Any] = field(default_factory=dict)
    updated_at: int = 0
    updated_label: str = ""
    is_wrapper_cache: bool | None = None
    component: str = ""
    source_component_prefix: bool | None = None


def escape(s: Any) -> str:
    return html.escape(str(s or ""), quote=True)


def strip_backticks(s: str) -> str:
    return s[1:-1] if s.startswith('`') and s.endswith('`') else s


def slug(s: str) -> str:
    s = s.replace("'", "_prime")
    out = []
    for ch in s:
        if re.match(r"[A-Za-z0-9_.:-]", ch):
            out.append(ch)
        else:
            out.append(f"_u{ord(ch):04x}")
    return "decl-" + ("".join(out) or "anonymous")


def module_name_from_path(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def root_prefix_for(out_rel_path: str) -> str:
    depth = len(Path(out_rel_path).parts) - 1
    return "./" if depth <= 0 else "../" * depth


def clean_doc_comment(raw: str) -> str:
    raw = raw.strip()
    if raw.startswith('/--') or raw.startswith('/-!'):
        raw = raw[3:]
    if raw.endswith('-/'):
        raw = raw[:-2]
    return "\n".join(re.sub(r"^\s*\* ?", "", line).rstrip() for line in raw.strip().splitlines()).strip()


def attribute_block_start(lines: list[str], end_idx: int) -> int | None:
    """Return the start of an ``@[...]`` block ending on ``end_idx``."""
    closing = lines[end_idx].rfind("]")
    if closing < 0:
        return None
    trailing = lines[end_idx][closing + 1 :].strip()
    if trailing and not trailing.startswith("--"):
        return None
    depth = 0
    for line_idx in range(end_idx, max(-1, end_idx - 100), -1):
        line = lines[line_idx]
        for char_idx in range(len(line) - 1, -1, -1):
            char = line[char_idx]
            if char == "]":
                depth += 1
            elif char == "[":
                if depth == 0:
                    return None
                depth -= 1
                if (
                    depth == 0
                    and char_idx > 0
                    and line[char_idx - 1] == "@"
                    and not line[: char_idx - 1].strip()
                ):
                    return line_idx
        if depth == 0:
            return None
    return None


def attached_doc_span(
    lines: list[str],
    start_idx: int,
) -> tuple[int, int] | None:
    """Return the line span of the doc comment attached to a declaration.

    In particular, do not search backwards through a ``/-! ... -/`` section
    heading and accidentally attach an older declaration comment and all code
    between it and the new declaration.
    """
    j = start_idx - 1
    while True:
        while j >= 0 and not lines[j].strip():
            j -= 1
        if j < 0:
            return None
        attribute_start = attribute_block_start(lines, j)
        if attribute_start is None:
            break
        j = attribute_start - 1

    if "-/" not in lines[j]:
        return None

    depth = 0
    end_idx = j
    marker_re = re.compile(r"/-|-/")
    for line_idx in range(j, -1, -1):
        markers = list(marker_re.finditer(lines[line_idx]))
        for marker in reversed(markers):
            if marker.group(0) == "-/":
                depth += 1
                continue
            if depth == 0:
                continue
            depth -= 1
            if depth == 0:
                if not lines[line_idx].startswith("/--", marker.start()):
                    return None
                return line_idx, end_idx
    return None


def find_doc_before(lines: list[str], start_idx: int) -> str:
    span = attached_doc_span(lines, start_idx)
    if span is None:
        return ""
    start, end = span
    return clean_doc_comment("\n".join(lines[start : end + 1]))


def declaration_prefix_lines(
    lines: list[str],
    scan_lines: list[str],
    start_idx: int,
) -> list[str]:
    """Return scoped wrappers and attributes belonging to a declaration.

    Doc comments remain in the prose panel, but commands such as ``omit ... in``
    and attributes such as ``@[simp]`` are part of the Lean statement and must
    not disappear from declaration cards.
    """
    j = start_idx - 1
    while j >= 0 and not lines[j].strip():
        j -= 1

    attribute_blocks: list[list[str]] = []
    while j >= 0:
        attribute_start = attribute_block_start(lines, j)
        if attribute_start is None:
            break
        attribute_blocks.append(lines[attribute_start : j + 1])
        j = attribute_start - 1
        while j >= 0 and not lines[j].strip():
            j -= 1

    doc_span = attached_doc_span(lines, start_idx)
    if doc_span is not None:
        j = doc_span[0] - 1
        while j >= 0 and not lines[j].strip():
            j -= 1

    wrapper_blocks: list[list[str]] = []
    while j >= 0:
        wrapper_start = declaration_wrapper_block_start(scan_lines, j)
        if wrapper_start is None:
            break
        wrapper_blocks.append(lines[wrapper_start : j + 1])
        j = wrapper_start - 1
        while j >= 0 and not lines[j].strip():
            j -= 1

    prefix: list[str] = []
    for block in reversed(wrapper_blocks):
        prefix.extend(block)
    for block in reversed(attribute_blocks):
        prefix.extend(block)
    return prefix


def declaration_wrapper_block_start(
    scan_lines: list[str],
    end_idx: int,
) -> int | None:
    """Find a possibly multiline ``... in`` command wrapper ending at a line."""
    if end_idx < 0 or not re.search(r"\bin\s*$", scan_lines[end_idx]):
        return None
    for line_idx in range(end_idx, max(-1, end_idx - 100), -1):
        line = scan_lines[line_idx]
        if not line.strip():
            return None
        if DECLARATION_WRAPPER_START_RE.match(line):
            start_indent = len(line) - len(line.lstrip(" \t"))
            if all(
                len(scan_lines[index])
                - len(scan_lines[index].lstrip(" \t"))
                > start_indent
                for index in range(line_idx + 1, end_idx + 1)
            ):
                return line_idx
            return None
        if (
            DECL_RE.match(line)
            or NS_RE.match(line)
            or END_RE.match(line)
            or line.lstrip().startswith(("/-", "--", "@["))
        ):
            return None
    return None


def extract_module_doc(lines: list[str]) -> str:
    scan_lines = stripped_code_lines_for_parsing(lines)
    first_declaration = next(
        (
            index
            for index, line in enumerate(scan_lines)
            if DECL_RE.match(line)
        ),
        len(lines),
    )
    m = re.search(
        r"/-!([\s\S]*?)-/",
        "\n".join(lines[:first_declaration]),
    )
    return clean_doc_comment(m.group(0)) if m else ""


def extract_name(
    kind: str,
    rest: str,
    namespaces: list[str],
    line_no: int,
    module: str = "",
) -> str:
    rest = rest.strip()
    if kind == "example":
        token = f"example_{line_no}"
        synthetic = True
    elif kind == "macro":
        macro_name = re.match(r'^"((?:\\.|[^"])*)"', rest)
        token = macro_name.group(1) if macro_name else f"macro_{line_no}"
        synthetic = macro_name is None
    elif kind == "instance":
        rest = re.sub(
            r"^\(\s*priority\s*:=\s*[^)]*\)\s*",
            "",
            rest,
        )
        m = IDENT_RE.match(rest)
        if m and not rest[m.start(1):].lstrip().startswith((":", "[", "{")):
            token = strip_backticks(m.group(1))
            synthetic = False
        else:
            token = f"inst_{line_no}"
            synthetic = True
    else:
        m = IDENT_RE.match(rest)
        token = strip_backticks(m.group(1)) if m else f"anonymous_{line_no}"
        synthetic = m is None
    if token.startswith("_root_."):
        return token[len("_root_."):]
    if synthetic and module:
        return f"{module}.{token}"
    if namespaces:
        ns = ".".join(namespaces)
        return token if token == ns or token.startswith(ns + ".") else ".".join(namespaces + [token])
    return token


def lean_code_without_comments_or_strings(source: str) -> str:
    """Blank Lean comments and string contents while preserving positions and newlines.

    Lean block comments nest.  Treating them as a single ``/- ... -/`` span, or
    recognizing comment markers inside strings, creates phantom declarations and
    imports in the documentation parser.
    """
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        char = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""
        if block_depth:
            if char == "/" and following == "-":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
                continue
            if char == "-" and following == "/":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
                continue
            output.append("\n" if char == "\n" else " ")
            index += 1
            continue
        if in_string:
            output.append("\n" if char == "\n" else " ")
            if char == "\\" and not escaped:
                escaped = True
            else:
                if char == '"' and not escaped:
                    in_string = False
                escaped = False
            index += 1
            continue
        if char == '"':
            in_string = True
            escaped = False
            output.append(" ")
            index += 1
            continue
        if char == "-" and following == "-":
            output.extend((" ", " "))
            index += 2
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
            continue
        if char == "/" and following == "-":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
            continue
        output.append(char)
        index += 1
    return "".join(output)


def stripped_code_lines_for_parsing(lines: list[str]) -> list[str]:
    """Return position-preserving, comment/string-free Lean source lines."""
    if not lines:
        return []
    return lean_code_without_comments_or_strings("\n".join(lines)).split("\n")


def declaration_end(lines: list[str], start: int, scan_lines: list[str] | None = None) -> int:
    scan_lines = scan_lines or stripped_code_lines_for_parsing(lines)
    start_indent = len(lines[start]) - len(lines[start].lstrip(" \t"))

    for j in range(start + 1, len(lines)):
        raw = lines[j]
        stripped = raw.lstrip()
        indent = len(raw) - len(stripped)
        if indent > start_indent:
            continue
        is_trivia_boundary = stripped.startswith(("/-", "--", "@["))
        is_code_boundary = bool(
            DECL_RE.match(scan_lines[j])
            or NS_RE.match(scan_lines[j])
            or END_RE.match(scan_lines[j])
            or TOPLEVEL_BOUNDARY_RE.match(scan_lines[j])
        )
        if is_trivia_boundary or is_code_boundary:
            end = j
            while end > start + 1 and not lines[end - 1].strip():
                end -= 1
            return end
    end = len(lines)
    while end > start + 1 and not lines[end - 1].strip():
        end -= 1
    return end


def parse_lean_file(
    path: Path,
    root: Path,
    *,
    source_root: Path | None = None,
    component: str = "",
    source_component_prefix: bool | None = None,
) -> Module:
    source = path.read_text(encoding="utf-8")
    lines = source.splitlines()
    scan_lines = stripped_code_lines_for_parsing(lines)
    module = module_name_from_path(path, root)
    rel_path = path.relative_to(source_root or root).as_posix()
    imports = [m.group(1) for line in scan_lines if (m := IMPORT_RE.match(line))]
    scopes: list[tuple[str, list[str]]] = []
    decls: list[Declaration] = []
    for i, line in enumerate(scan_lines):
        if m := NS_RE.match(line):
            scopes.append(("namespace", m.group(1).split('.')))
            continue
        if SECTION_RE.match(line):
            scopes.append(("section", []))
            continue
        if MUTUAL_RE.match(line):
            scopes.append(("mutual", []))
            continue
        if m_end := END_RE.match(line):
            if scopes:
                scopes.pop()
            continue
        m = DECL_RE.match(line)
        if not m:
            continue
        if re.search(r"\bprivate\b", line[:m.start("kind")]):
            continue
        kind = m.group("kind")
        namespaces = [part for scope, parts in scopes if scope == "namespace" for part in parts]
        if kind == "macro":
            raw_macro_name = re.search(
                r'\bmacro\s+("((?:\\.|[^"])*)")',
                lines[i],
            )
            name_source = raw_macro_name.group(1) if raw_macro_name else ""
        else:
            name_source = "\n".join(
                [m.group("rest"), *scan_lines[i + 1 : i + 6]]
            )
        full_name = extract_name(
            kind,
            name_source,
            namespaces,
            i + 1,
            module,
        )
        end = declaration_end(lines, i, scan_lines)
        prefix = declaration_prefix_lines(lines, scan_lines, i)
        decls.append(Declaration(
            kind=kind,
            name=full_name.split('.')[-1],
            full_name=full_name,
            line=i + 1,
            code="\n".join([*prefix, *lines[i:end]]).rstrip(),
            doc=find_doc_before(lines, i),
            module=module,
            rel_path=rel_path,
            id=slug(full_name),
            component=component,
            source_component_prefix=source_component_prefix,
        ))
    return Module(
        module,
        rel_path,
        source,
        imports,
        extract_module_doc(lines),
        decls,
        component=component,
        source_component_prefix=source_component_prefix,
    )


def split_lean_statement_proof(code: str) -> tuple[str, str]:
    scan = lean_code_without_comments_or_strings(code)
    depth = 0
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closing = set(pairs.values())
    only_whitespace_on_line = True
    pending_top_level_lets = 0
    top_level_match = False
    pending_pattern_fun = False

    def is_identifier_character(ch: str) -> bool:
        return ch.isalnum() or ch in "_'.?!"

    i = 0
    while i < len(scan):
        ch = scan[i]
        if ch in pairs:
            depth += 1
            pending_pattern_fun = False
        elif ch in closing and depth > 0:
            depth -= 1
        elif depth == 0 and is_identifier_character(ch):
            token_end = i + 1
            while (
                token_end < len(scan)
                and is_identifier_character(scan[token_end])
            ):
                token_end += 1
            token = scan[i:token_end]
            if token in {"let", "letI"}:
                pending_top_level_lets += 1
            if token == "match":
                top_level_match = True
            if token == "fun":
                pending_pattern_fun = True
            elif pending_pattern_fun:
                pending_pattern_fun = False
            only_whitespace_on_line = False
            i = token_end
            continue
        elif (
            ch == ":"
            and i + 1 < len(scan)
            and scan[i + 1] == "="
            and depth == 0
        ):
            if pending_top_level_lets:
                pending_top_level_lets -= 1
                i += 2
                continue
            return code[:i].rstrip(), code[i + 2:].strip()
        elif ch == "|" and depth == 0 and only_whitespace_on_line:
            if top_level_match or pending_pattern_fun:
                pending_pattern_fun = False
            else:
                return code[:i].rstrip(), code[i:].strip()
        elif depth == 0 and pending_pattern_fun and not ch.isspace():
            pending_pattern_fun = False

        if ch == "\n":
            only_whitespace_on_line = True
        elif not ch.isspace():
            only_whitespace_on_line = False
        i += 1
    return code.rstrip(), ""


def is_proof_kind(kind: str) -> bool:
    return kind in PROOF_KINDS


def lean_parts_for_decl(decl: Declaration) -> tuple[str, str]:
    return split_lean_statement_proof(decl.code) if is_proof_kind(decl.kind) else (decl.code.rstrip(), "")


def kind_label(kind: str) -> str:
    return KIND_LABELS.get(kind, kind)






def first_natural_statement(module: Module) -> str:
    for d in module.decls:
        stmt = str((d.natural or {}).get("statement", "") or "").strip()
        if stmt:
            return stmt
    return ""




def component_for_module_name(
    module_name: str,
    module_components: dict[str, str] | None = None,
) -> str:
    return (module_components or {}).get(module_name, "")


def render_module_breadcrumb(
    module_name: str,
    module_names: set[str],
    root: str,
    *,
    source: bool = False,
    module_components: dict[str, str] | None = None,
) -> str:
    parts = module_name.split(".")
    crumbs: list[str] = []
    for idx in range(1, len(parts) + 1):
        name = ".".join(parts[:idx])
        label = name if idx == 1 else parts[idx - 1]
        is_current = idx == len(parts) and not source
        if name in module_names and not is_current:
            target = module_html_path(
                name,
                component_for_module_name(name, module_components),
            )
            crumbs.append(f'<a href="{escape(root + target)}">{escape(label)}</a>')
        else:
            crumbs.append(f'<span>{escape(label)}</span>')
    if source:
        crumbs.append("<span>Source</span>")
    return '<div class="eyebrow breadcrumb">' + '<span class="sep">/</span>'.join(crumbs) + '</div>'




def overview_text_key(text: str) -> str:
    text = str(text or "").strip()
    text = re.sub(r"(?m)^\s*[-*]\s+", "", text)
    return re.sub(r"\s+", " ", text).strip()




def library_name(module_name: str) -> str:
    return module_name.split('.')[0] if module_name else ""


def group_modules_by_library(modules: list[Module]) -> dict[str, list[Module]]:
    grouped: dict[str, list[Module]] = defaultdict(list)
    for module in modules:
        grouped[library_name(module.name)].append(module)
    return {k: sorted(v, key=lambda m: m.name.lower()) for k, v in sorted(grouped.items(), key=lambda x: x[0].lower())}


def module_remainder(module_name: str, prefix: str) -> str:
    dotted = prefix + '.'
    if module_name.startswith(dotted):
        return module_name[len(dotted):]
    return ""


def direct_child_name(module_name: str, prefix: str) -> str:
    remainder = module_remainder(module_name, prefix)
    return remainder.split('.', 1)[0] if remainder else ""


def group_modules_by_direct_child(modules: list[Module], prefix: str) -> dict[str, list[Module]]:
    grouped: dict[str, list[Module]] = defaultdict(list)
    for module in modules:
        child = direct_child_name(module.name, prefix)
        if child:
            grouped[child].append(module)
    return {
        key: sorted(value, key=lambda m: (m.name.count('.'), m.name.lower()))
        for key, value in sorted(grouped.items(), key=lambda item: item[0].lower())
    }


def count_decls(decls: Iterable[Declaration], kinds: set[str] | None = None) -> int:
    if kinds is None:
        return sum(1 for _ in decls)
    return sum(1 for d in decls if d.kind in kinds)


def count_sorry_tokens(source: str) -> int:
    total = 0
    for _, line in code_lines_without_line_comments(source):
        total += len(SORRY_TOKEN_RE.findall(line))
    return total


def count_label(
    count: int,
    singular: str,
    plural: str | None = None,
) -> str:
    return f"{count} {singular if count == 1 else (plural or singular + 's')}"


def kind_count_label(kind: str, count: int) -> str:
    label = (
        kind_label(kind)
        if count == 1
        else KIND_PLURAL_LABELS.get(kind, kind_label(kind) + "s")
    )
    return f"{count} {label}"




def kind_summary(decls: Iterable[Declaration]) -> str:
    decls = list(decls)
    if not decls:
        return "No declarations"
    order = [
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "structure",
        "class",
        "inductive",
        "instance",
        "axiom",
        "constant",
        "opaque",
        "example",
        "macro",
    ]
    counts = Counter(d.kind for d in decls)
    parts = [kind_count_label(k, counts[k]) for k in order if counts.get(k)]
    parts.extend(
        kind_count_label(k, v)
        for k, v in sorted(counts.items())
        if k not in order
    )
    return " | ".join(parts)


def truncate_text(text: Any, limit: int = 180) -> str:
    text = re.sub(r"\s+", " ", str(text or "")).strip()
    return text if len(text) <= limit else text[: max(0, limit - 3)] + "..."


def module_note(module: Module) -> str:
    explicit = str((module.natural or {}).get("summary", "") or "").strip()
    if explicit:
        return explicit
    sample = first_natural_statement(module)
    return sample if sample else "Contents: " + kind_summary(module.decls)


def overview_compare_key(text: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "", overview_text_key(text).lower())


def normalize_module_blurb(text: Any) -> str:
    raw = str(text or "").replace("\r\n", "\n").strip()
    if not raw:
        return ""
    paragraphs: list[str] = []
    for block in re.split(r"\n\s*\n", raw):
        lines = []
        for line in block.splitlines():
            stripped = line.strip()
            if not stripped or stripped.startswith("#"):
                continue
            lines.append(stripped)
        if lines:
            paragraphs.append(" ".join(lines))
    return "\n\n".join(paragraphs)


def module_doc_natural_entry(module_doc: str) -> dict[str, str]:
    """Build public module prose from the parsed Lean module doc comment."""
    statement = normalize_module_blurb(module_doc)
    if not statement:
        return {}
    summary = statement.split("\n\n", 1)[0]
    return {"summary": summary, "statement": statement}


def declaration_doc_natural_entry(doc: str) -> dict[str, str]:
    """Build a public declaration statement from its parsed Lean doc comment."""
    statement = str(doc or "").strip()
    return {"statement": statement} if statement else {}


def is_generic_module_blurb(text: str, module_name: str = "") -> bool:
    lowered = normalize_module_blurb(text).lower()
    if not lowered:
        return True
    if lowered.startswith("contents: "):
        return True
    if any(
        phrase in lowered
        for phrase in (
            "import aggregator",
            "this module collects imports",
            "this file collects imports",
            "this module bundles imports",
            "this file bundles imports",
        )
    ):
        return True
    simple_name = module_name.split(".")[-1].replace("_", " ").lower()
    return bool(simple_name and lowered == simple_name)


def ancestor_module_names(module_name: str) -> list[str]:
    parts = module_name.split(".")
    return [".".join(parts[:idx]) for idx in range(1, len(parts))]


def ancestor_overview_keys(module: Module, modules_by_name: dict[str, Module]) -> set[str]:
    keys: set[str] = set()
    for name in ancestor_module_names(module.name):
        ancestor = modules_by_name.get(name)
        if ancestor is None:
            continue
        key = overview_compare_key(normalize_module_blurb(ancestor.module_doc))
        if key:
            keys.add(key)
    return keys


def module_specific_blurb(
    module: Module,
    modules_by_name: dict[str, Module],
) -> str:
    text = normalize_module_blurb(module.module_doc)
    key = overview_compare_key(text)
    title_key = overview_compare_key(module.name)
    ancestor_keys = ancestor_overview_keys(module, modules_by_name)
    if not key or key == title_key or key in ancestor_keys or is_generic_module_blurb(text, module.name):
        return ""
    return text


def module_card_note(module: Module, modules_by_name: dict[str, Module]) -> str:
    return module_specific_blurb(module, modules_by_name)


def strip_paragraph_wrapper(html_text: str) -> str:
    text = html_text.strip()
    if text.startswith("<p>") and text.endswith("</p>"):
        return text[3:-4]
    return text


def module_overview_text(
    module: Module,
    modules_by_name: dict[str, Module],
) -> str:
    blurb = module_specific_blurb(module, modules_by_name)
    if blurb:
        return blurb
    return f"Import surface for `{module.name}`." if is_wrapper_module(module) else ""


def is_broad_wrapper_note(text: str) -> bool:
    lowered = normalize_module_blurb(text).lower()
    if not lowered:
        return True
    return "together with" in lowered or lowered.count(",") >= 4


def child_group_note(
    note_source: Module,
    child_modules: list[Module],
    modules_by_name: dict[str, Module],
    root: str,
    depth: int = 0,
) -> str:
    note = module_card_note(note_source, modules_by_name)
    if not is_wrapper_module(note_source) or not is_broad_wrapper_note(note) or depth >= 2:
        return note
    nested = module_child_highlights(note_source, child_modules, modules_by_name, root, limit=1, depth=depth + 1)
    if nested:
        return nested[0][2]
    return note


def module_child_highlights(
    module: Module,
    modules: list[Module],
    modules_by_name: dict[str, Module],
    root: str,
    limit: int = 4,
    depth: int = 0,
) -> list[tuple[str, str, str]]:
    highlights: list[tuple[str, str, str]] = []
    for child, child_modules in group_modules_by_direct_child(modules, module.name).items():
        anchor = child_anchor_module(module.name, child, child_modules)
        content_modules = [item for item in child_modules if not is_wrapper_module(item)]
        note_source = anchor or next((item for item in content_modules if module_card_note(item, modules_by_name)), None)
        if note_source is None:
            note_source = child_modules[0]
        note = child_group_note(note_source, child_modules, modules_by_name, root, depth=depth)
        if note:
            target_name = anchor.name if anchor else note_source.name
            target = modules_by_name[target_name]
            highlights.append(
                (child, root + module_html_path(target.name, target.component), note)
            )
        if len(highlights) >= limit:
            break
    return highlights


def render_module_overview(
    module: Module,
    modules_by_name: dict[str, Module],
) -> str:
    text = module_overview_text(module, modules_by_name)
    if not text:
        return ""
    return (
        '<div class="module-overview tex2jax_process">'
        f"{simple_markdown(text)}</div>"
    )


def is_wrapper_module(module: Module) -> bool:
    if module.is_wrapper_cache is not None:
        return module.is_wrapper_cache
    if module.decls or not module.imports:
        module.is_wrapper_cache = False
        return False
    for _line_no, line in code_lines_without_line_comments(module.source):
        stripped = line.strip()
        if stripped and not IMPORT_RE.match(stripped):
            module.is_wrapper_cache = False
            return False
    module.is_wrapper_cache = True
    return True


def timestamp_label(timestamp: int) -> str:
    if timestamp <= 0:
        return ""
    return datetime.fromtimestamp(timestamp, timezone.utc).strftime("%Y-%m-%d")


def timestamp_epoch(value: str) -> int:
    """Parse the deterministic publish timestamp used for generated module metadata."""
    text = str(value or "").strip()
    if not text:
        return 0
    normalized = text[:-1] + "+00:00" if text.endswith("Z") else text
    try:
        parsed = datetime.fromisoformat(normalized)
    except ValueError as error:
        raise ValueError(f"invalid ISO-8601 generated timestamp: {value!r}") from error
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return int(parsed.timestamp())


def git_updated_at_map(lean_root: Path, rel_paths: list[str]) -> dict[str, int]:
    if not rel_paths:
        return {}
    try:
        prefix_proc = subprocess.run(
            ["git", "-C", str(lean_root), "rev-parse", "--show-prefix"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return {}
    if prefix_proc.returncode != 0:
        return {}

    prefix = prefix_proc.stdout.strip().replace("\\", "/")
    wanted = set(rel_paths)
    try:
        proc = subprocess.run(
            ["git", "-C", str(lean_root), "log", "--format=%ct", "--name-only", "--", *rel_paths],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=20,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return {}
    if proc.returncode != 0:
        return {}

    out: dict[str, int] = {}
    current_timestamp = 0
    for raw in proc.stdout.splitlines():
        line = raw.strip().replace("\\", "/")
        if not line:
            continue
        if line.isdigit():
            current_timestamp = int(line)
            continue
        rel = line
        if prefix and rel.startswith(prefix):
            rel = rel[len(prefix):]
        if current_timestamp and rel in wanted and rel not in out:
            out[rel] = current_timestamp
            if len(out) == len(wanted):
                break
    return out


def file_mtime(lean_root: Path, rel_path: str) -> int:
    try:
        return int((lean_root / rel_path).stat().st_mtime)
    except OSError:
        return 0


def declaration_lookup(modules: list[Module]) -> dict[str, Declaration]:
    by_full: dict[str, Declaration] = {}
    for module in modules:
        for declaration in module.decls:
            previous = by_full.get(declaration.full_name)
            if previous is not None:
                raise ValueError(
                    "duplicate generated declaration name "
                    f"{declaration.full_name!r}: "
                    f"{previous.rel_path}:{previous.line} and "
                    f"{declaration.rel_path}:{declaration.line}"
                )
            by_full[declaration.full_name] = declaration
    return by_full


def decl_url(decl: Declaration, root: str) -> str:
    return root + module_html_path(decl.module, decl.component) + '#' + decl.id


def link_map_for(by_token: dict[str, Declaration], root: str) -> dict[str, str]:
    return {
        token: decl_url(decl, root)
        for token, decl in by_token.items()
        if "." in token
    }


def cached_link_map_for(
    by_token: dict[str, Declaration],
    root: str,
    cache: dict[str, dict[str, str]] | None = None,
) -> dict[str, str]:
    if cache is None:
        return link_map_for(by_token, root)
    links = cache.get(root)
    if links is None:
        links = link_map_for(by_token, root)
        cache[root] = links
    return links


def simple_markdown(text: Any) -> str:
    if isinstance(text, list):
        text = "\n\n".join(str(x) for x in text)
    elif isinstance(text, dict):
        text = "\n\n".join(f"{k}: {v}" for k, v in text.items())
    text = str(text or "").strip()
    if not text:
        return ""

    def markdown_link(match: re.Match[str]) -> str:
        label, target = match.groups()
        decoded_target = html.unescape(target).strip()
        is_link = bool(
            re.match(r"^(?:https?://|mailto:|#|/|\./|\.\./)", decoded_target)
            or decoded_target.endswith((".html", ".htm", ".md"))
        )
        if not is_link:
            return match.group(0)
        return f'<a href="{escape(decoded_target)}">{label}</a>'

    def inline(s: str) -> str:
        e = escape(s)
        e = re.sub(r"`([^`]+)`", r"<code>\1</code>", e)
        e = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", e)
        e = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", markdown_link, e)
        return e

    blocks: list[str] = []
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        if not lines[i].strip():
            i += 1
            continue
        if lines[i].lstrip().startswith('- '):
            items = []
            while i < len(lines) and lines[i].lstrip().startswith('- '):
                items.append('<li>' + inline(lines[i].lstrip()[2:].strip()) + '</li>')
                i += 1
            blocks.append('<ul>' + ''.join(items) + '</ul>')
            continue
        para = []
        while i < len(lines) and lines[i].strip() and not lines[i].lstrip().startswith('- '):
            para.append(lines[i].strip())
            i += 1
        blocks.append('<p>' + inline(' '.join(para)) + '</p>')
    return "\n".join(blocks)


def highlight_lean(code: str, link_map: dict[str, str] | None = None, skip: set[str] | None = None) -> str:
    skip = skip or set()

    def render_token(token: str) -> str:
        shown = escape(token)
        if token in KEYWORDS:
            return f'<span class="kw">{shown}</span>'
        if link_map and token not in skip and token in link_map:
            return f'<a class="decl-ref" href="{escape(link_map[token])}">{shown}</a>'
        return shown

    rendered: list[str] = []
    block_depth = 0
    in_string = False
    string_escaped = False
    for raw_line in code.splitlines():
        out: list[str] = []
        i = 0
        while i < len(raw_line):
            if block_depth:
                start = i
                while i < len(raw_line):
                    if raw_line.startswith('/-', i):
                        block_depth += 1
                        i += 2
                    elif raw_line.startswith('-/', i):
                        block_depth -= 1
                        i += 2
                        if block_depth == 0:
                            break
                    else:
                        i += 1
                out.append('<span class="comment">' + escape(raw_line[start:i]) + '</span>')
                continue

            if in_string:
                start = i
                while i < len(raw_line):
                    ch = raw_line[i]
                    i += 1
                    if ch == '"' and not string_escaped:
                        in_string = False
                        string_escaped = False
                        break
                    if ch == '\\' and not string_escaped:
                        string_escaped = True
                    else:
                        string_escaped = False
                out.append('<span class="str">' + escape(raw_line[start:i]) + '</span>')
                continue

            if raw_line.startswith('--', i):
                out.append('<span class="comment">' + escape(raw_line[i:]) + '</span>')
                i = len(raw_line)
                continue

            if raw_line.startswith('/-', i):
                start = i
                block_depth = 1
                i += 2
                while i < len(raw_line):
                    if raw_line.startswith('/-', i):
                        block_depth += 1
                        i += 2
                    elif raw_line.startswith('-/', i):
                        block_depth -= 1
                        i += 2
                        if block_depth == 0:
                            break
                    else:
                        i += 1
                out.append('<span class="comment">' + escape(raw_line[start:i]) + '</span>')
                continue

            if raw_line[i] == '"':
                start = i
                in_string = True
                string_escaped = False
                i += 1
                while i < len(raw_line):
                    ch = raw_line[i]
                    i += 1
                    if ch == '"' and not string_escaped:
                        in_string = False
                        string_escaped = False
                        break
                    if ch == '\\' and not string_escaped:
                        string_escaped = True
                    else:
                        string_escaped = False
                out.append(
                    '<span class="str">'
                    + escape(raw_line[start:i])
                    + "</span>"
                )
                continue

            m = TOKEN_RE.match(raw_line, i)
            if m:
                token = m.group(0)
                out.append(render_token(token))
                i = m.end()
            else:
                out.append(escape(raw_line[i]))
                i += 1
        rendered.append(''.join(out))
        if in_string:
            string_escaped = False
    return "\n".join(rendered)


def code_lines_without_line_comments(source: str) -> Iterable[tuple[int, str]]:
    for i, line in enumerate(
        lean_code_without_comments_or_strings(source).splitlines(), start=1
    ):
        yield i, line


def source_link_url(
    root: str,
    rel_path: str,
    line: int,
    source_base_url: str = "",
    component: str = "",
    strip_component_prefix: bool | None = None,
) -> str:
    if source_base_url:
        return source_base_url.rstrip('/') + '/' + rel_path + f'#L{line}'
    return (
        root
        + source_html_path(rel_path, component, strip_component_prefix)
        + f'#L{line}'
    )


def source_link_label(source_base_url: str = '') -> str:
    return "GitHub" if source_base_url else "Source"


def header(title: str, root: str, label: str = "") -> str:
    nav = (
        '<a href="https://github.com/n-yamaguchi-0729/ProCGroups" '
        'target="_blank" rel="noopener">GitHub repository</a>'
    )
    current = (
        f'<div class="header-current">{escape(label)}</div>'
        if label else '<div class="header-current" aria-hidden="true"></div>'
    )
    return f'''<header class="site-header">
  <a class="brand" href="{escape(root)}index.html">{escape(title)}</a>
  <nav class="header-nav">{nav}</nav>
  {current}
  <form class="search-form" action="{escape(root)}find/index.html" method="get" autocomplete="off">
    <input id="search_input" name="pattern" placeholder="Search names and statements" aria-label="Search">
    <div id="autocomplete_results" class="autocomplete"></div>
  </form>
</header>'''


def scripts(root: str) -> str:
    return f'<script defer src="{escape(root)}assets/site.js" data-root="{escape(root)}"></script>'


def clean_generated_html(content: str) -> str:
    lines: list[str] = []
    in_pre = False
    in_script = False
    for raw_line in content.splitlines():
        line = raw_line.rstrip()
        lower = line.lower()
        if "<pre" in lower:
            in_pre = True
        if "<script" in lower:
            in_script = True
        if line or in_pre or in_script:
            lines.append(line)
        if "</pre>" in lower:
            in_pre = False
        if "</script>" in lower:
            in_script = False
    return "\n".join(lines).rstrip() + "\n"


def full_page(
    page_title: str,
    root: str,
    body: str,
    label: str = "",
    body_class: str = "",
    site_title: str = "ProCGroups Documentation",
    description: str = "",
    canonical_url: str = "",
    render_math: bool = False,
    force_math: bool = False,
) -> str:
    body_classes = " ".join(
        item for item in ("tex2jax_ignore", body_class) if item
    )
    body_attr = f' class="{escape(body_classes)}"'
    description_tag = f'<meta name="description" content="{escape(description)}">\n' if description else ""
    canonical_tag = f'<link rel="canonical" href="{escape(canonical_url)}">\n' if canonical_url else ""
    math_tag = (
        MATHJAX_TAG + "\n"
        if render_math and (force_math or r"\(" in body or r"\[" in body)
        else ""
    )
    return f'''<!doctype html>
<html lang="en">
<head>
{GOOGLE_TAG}
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{escape(page_title)}</title>
{description_tag}{canonical_tag}{math_tag}<link rel="stylesheet" href="{escape(root)}assets/site.css">
</head>
<body{body_attr}>
{header(site_title, root, label)}
{body}
{scripts(root)}
</body>
</html>'''


def shell(content: str, active_module: str = "") -> str:
    return f'''<div class="layout">
  <main class="main">{content}</main>
  <aside class="file-tree" data-active="{escape(active_module)}"><div class="tree-pane">
    <div class="tree-title">Files</div>
    <div id="file_tree"><div class="tree-loading">Loading</div></div>
  </div></aside>
</div>'''


def natural_statement_html(decl: Declaration) -> str:
    statement = (decl.natural or {}).get("statement", "") or ""
    statement = re.sub(r"^\s*(?:Statement|主張)[.．。]\s*", "", str(statement or "").strip())
    return simple_markdown(statement) if statement else ""


def render_module_imports(
    module: Module,
    module_names: set[str],
    root: str,
    module_components: dict[str, str] | None = None,
    *,
    expanded: bool = False,
) -> str:
    lis = []
    for imp in module.imports:
        target = module_html_path(
            imp,
            component_for_module_name(imp, module_components),
        )
        item = (
            f'<a href="{escape(root + target)}">{escape(imp)}</a>'
            if imp in module_names
            else escape(imp)
        )
        lis.append(f'<li>{item}</li>')
    content = f'<ul>{"".join(lis)}</ul>' if lis else '<div class="imports-empty">None</div>'
    open_attr = " open" if expanded else ""
    summary = "import" if len(module.imports) == 1 else "imports"
    return (
        f'<details class="imports"{open_attr}>'
        f"<summary>{summary}</summary>{content}</details>"
    )


def render_imported_by(
    module: Module,
    root: str,
    module_components: dict[str, str] | None = None,
) -> str:
    lis = "".join(
        f'<li><a href="{escape(root + module_html_path(name, component_for_module_name(name, module_components)))}">{escape(name)}</a></li>'
        for name in module.imported_by
    )
    content = f'<ul>{lis}</ul>' if lis else '<div class="imports-empty">None</div>'
    return f'<details class="imports"><summary>Imported by</summary>{content}</details>'


def relative_module_name(module_name: str, prefix: str) -> str:
    remainder = module_remainder(module_name, prefix)
    return remainder or module_name


def child_anchor_module(parent_name: str, child_name: str, modules: list[Module]) -> Module | None:
    target = f"{parent_name}.{child_name}"
    return next((module for module in modules if module.name == target), None)




def render_decl(decl: Declaration, root: str, link_map: dict[str, str], source_base_url: str = "") -> str:
    lean_statement, lean_proof = lean_parts_for_decl(decl)
    skip = {decl.full_name, decl.name}
    source = source_link_url(
        root,
        decl.rel_path,
        decl.line,
        source_base_url,
        decl.component,
        decl.source_component_prefix,
    )
    source_link = f'<a class="source-link" href="{escape(source)}">{source_link_label(source_base_url)}</a>' if source else ''
    has_proof_section = is_proof_kind(decl.kind) and bool(lean_proof.strip())
    proof_html = ""
    if has_proof_section:
        lean_proof_html = highlight_lean(lean_proof, link_map, skip)
        proof_html = f'''
  <details class="proof-details">
    <summary><span class="summary-text">Show Lean proof</span></summary>
    <template class="proof-template">
      <pre class="code-box lean-proof-code"><code>{lean_proof_html}</code></pre>
    </template>
    <div class="proof-mount"></div>
  </details>'''
    natural_html = natural_statement_html(decl)
    pair_class = "pair statement-pair" if natural_html else "pair statement-pair statement-only"
    natural_section = (
        '<section><div class="natural-text tex2jax_process">'
        f"{natural_html}</div></section>"
        if natural_html
        else ""
    )
    return f'''<section class="decl {escape(decl.kind)}" id="{escape(decl.id)}">
  <div class="decl-head">
    <span class="kind {escape(decl.kind)}">{escape(kind_label(decl.kind))}</span>
    <a class="decl-name" href="#{escape(decl.id)}">{escape(decl.full_name)}</a>
    {source_link}
  </div>
  <div class="{pair_class}">
    <section><pre class="code-box"><code>{highlight_lean(lean_statement, link_map, skip)}</code></pre></section>
    {natural_section}
  </div>{proof_html}
</section>'''














def build_search_index(
    modules: list[Module],
    component_display_names: dict[str, str] | None = None,
) -> list[dict[str, str]]:
    index: list[dict[str, str]] = []
    display_names = dict(component_display_names or {})
    for component in sorted({module.component for module in modules if module.component}):
        display_name = display_names.get(component, component)
        index.append({
            "n": display_name,
            "s": display_name,
            "k": "Library",
            "m": component,
            "u": f"index.html#library-{component}",
            "t": f"{display_name} library",
        })
    for m in modules:
        index.append({
            "n": m.name,
            "s": m.name.split('.')[-1],
            "k": "Lean file",
            "m": m.name,
            "u": module_html_path(m.name, m.component),
            "t": truncate_text(module_note(m), 220),
        })
        for d in m.decls:
            index.append({
                "n": d.full_name,
                "s": d.name,
                "k": kind_label(d.kind),
                "m": d.module,
                "u": module_html_path(d.module, d.component) + '#' + d.id,
                "t": truncate_text((d.natural or {}).get('statement', ''), 220),
            })
    return index


def record_generated_path(out_root: Path, path: Path, generated: set[str] | None) -> None:
    if generated is None:
        return
    try:
        generated.add(path.resolve().relative_to(out_root).as_posix())
    except ValueError:
        pass


def write_file(
    path: Path,
    content: str,
    *,
    out_root: Path | None = None,
    generated: set[str] | None = None,
    stats: WriteStats | None = None,
) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.suffix.lower() == ".html":
        content = clean_generated_html(content)
    if out_root is not None:
        record_generated_path(out_root, path, generated)
    if stats is not None:
        stats.generated += 1
    data = content.encode("utf-8")
    try:
        if path.exists() and path.read_bytes() == data:
            if stats is not None:
                stats.unchanged += 1
            return False
    except OSError:
        pass
    path.write_bytes(data)
    if stats is not None:
        stats.written += 1
    return True


def ensure_output_dir(out: Path) -> None:
    if out.exists() and not out.is_dir():
        raise NotADirectoryError(f"Output path exists but is not a directory: {out}")
    out.mkdir(parents=True, exist_ok=True)


def safe_output_path(out_root: Path, rel_path: str) -> Path:
    raw = str(rel_path)
    normalized_separators = raw.replace("\\", "/")
    segments = normalized_separators.split("/")
    if (
        not raw
        or any(segment in {"", ".", ".."} for segment in segments)
        or Path(raw).is_absolute()
        or PurePosixPath(normalized_separators).is_absolute()
        or re.match(r"^[A-Za-z]:", raw)
    ):
        raise ValueError(f"Invalid generated output path: {rel_path!r}")

    resolved_root = out_root.resolve()
    path = (resolved_root / Path(*segments)).resolve()
    if path == resolved_root or resolved_root not in path.parents:
        raise ValueError(f"Refusing to touch output outside {out_root}: {rel_path}")
    return path


def read_site_manifest(out_root: Path) -> set[str]:
    manifest = out_root / SITE_MANIFEST_NAME
    if not manifest.exists():
        return set()
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return set()
    files = data.get("files", []) if isinstance(data, dict) else []
    return {str(item) for item in files if isinstance(item, str)}


def write_site_manifest(out_root: Path, generated: set[str], generated_at: str) -> None:
    manifest_rel = SITE_MANIFEST_NAME
    generated = set(generated)
    generated.add(manifest_rel)
    data = {
        "version": 1,
        "generated_at": generated_at,
        "file_count": len(generated),
        "files": sorted(generated),
    }
    write_file(out_root / manifest_rel, json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def remove_generated_path(path: Path, stats: WriteStats | None = None) -> None:
    if not path.exists():
        return
    if path.is_dir():
        shutil.rmtree(path, onerror=remove_readonly)
    else:
        try:
            path.unlink()
        except PermissionError:
            remove_readonly(lambda target: Path(target).unlink(), str(path), None)
    if stats is not None:
        stats.deleted += 1


def remove_empty_output_parents(out_root: Path, path: Path) -> None:
    parent = path.parent
    while parent != out_root and out_root in parent.parents:
        try:
            parent.rmdir()
        except OSError:
            break
        parent = parent.parent


def pre_manifest_generated_roots(out_root: Path) -> list[Path]:
    # The current library directories are data-driven and the manifest handles
    # their stale outputs.  Only this pre-manifest root has no data-derived name.
    return [out_root / "src"]


def cleanup_stale_outputs(
    out_root: Path,
    previous: set[str],
    generated: set[str],
    stats: WriteStats,
    reporter: BuildReporter | None = None,
) -> None:
    stale = sorted(previous - generated - {SITE_MANIFEST_NAME}, key=lambda item: item.count("/"), reverse=True)
    for rel in stale:
        path = safe_output_path(out_root, rel)
        remove_generated_path(path, stats)
        remove_empty_output_parents(out_root, path)
    for path in pre_manifest_generated_roots(out_root):
        remove_generated_path(path, stats)
    if reporter:
        reporter.progress(f"Output cleanup: removed {stats.deleted} stale generated path(s)")


def should_skip_lean_path(path: Path, root: Path) -> bool:
    rel = path.relative_to(root)
    if rel.name in SKIP_LEAN_FILES:
        return True
    if any(part.startswith('.') or part in SKIP_LEAN_DIRS for part in rel.parts):
        return True
    return not is_safe_lean_source_path(path, root)


def lean_distribution_files(lean_root: Path) -> list[Path]:
    return [p for p in sorted(lean_root.rglob("*.lean")) if not should_skip_lean_path(p, lean_root)]


def lean_package_name(name: str) -> str:
    name = str(name or "").strip()
    return name if re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", name) else DEFAULT_LEAN_PACKAGE_NAME


def lean_toolchain_for_distribution(lean_root: Path, configured: str = "") -> str:
    return str(configured or "").strip() or detect_lean_toolchain(lean_root) or "leanprover/lean4:stable"


def write_distribution_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = content.encode("utf-8")
    try:
        if path.exists() and path.read_bytes() == data:
            return
    except OSError:
        pass
    path.write_bytes(data)


def copy_file_if_changed(src: Path, dest: Path) -> None:
    dest.parent.mkdir(parents=True, exist_ok=True)
    try:
        if dest.exists() and dest.stat().st_size == src.stat().st_size and dest.read_bytes() == src.read_bytes():
            return
    except OSError:
        pass
    shutil.copy2(src, dest)


def write_binary_file(
    path: Path,
    data: bytes,
    *,
    out_root: Path | None = None,
    generated: set[str] | None = None,
    stats: WriteStats | None = None,
) -> bool:
    path.parent.mkdir(parents=True, exist_ok=True)
    if out_root is not None:
        record_generated_path(out_root, path, generated)
    if stats is not None:
        stats.generated += 1
    try:
        if path.exists() and path.read_bytes() == data:
            if stats is not None:
                stats.unchanged += 1
            return False
    except OSError:
        pass
    path.write_bytes(data)
    if stats is not None:
        stats.written += 1
    return True


def validate_safe_directory_tree(
    root: Path, label: str, *, allow_missing: bool = False
) -> None:
    """Reject links and case-insensitive aliases before a recursive copy or archive."""
    if root.is_symlink():
        raise ValueError(f"{label} root must not be a symlink: {root}")
    if not root.exists():
        if allow_missing:
            return
        raise ValueError(f"{label} does not exist: {root}")
    if not root.is_dir():
        raise ValueError(f"{label} is not a directory: {root}")

    casefolded: dict[str, str] = {}
    problems: list[str] = []
    pending: list[tuple[Path, Path]] = [(root, Path())]
    while pending:
        directory, relative_directory = pending.pop()
        try:
            entries = sorted(os.scandir(directory), key=lambda entry: entry.name)
        except OSError as error:
            problems.append(f"cannot inspect {relative_directory.as_posix() or '.'}: {error}")
            continue
        for entry in entries:
            relative_path = relative_directory / entry.name
            relative = relative_path.as_posix()
            previous = casefolded.setdefault(relative.casefold(), relative)
            if previous != relative:
                problems.append(
                    f"case-insensitive path collision {previous!r} and {relative!r}"
                )
            try:
                if entry.is_symlink():
                    problems.append(f"symlink {relative!r}")
                elif entry.is_dir(follow_symlinks=False):
                    pending.append((Path(entry.path), relative_path))
                elif not entry.is_file(follow_symlinks=False):
                    problems.append(f"unsupported non-file entry {relative!r}")
            except OSError as error:
                problems.append(f"cannot inspect {relative!r}: {error}")
    if problems:
        raise ValueError(f"{label} contains unsafe entries: " + "; ".join(problems[:20]))


def zip_directory_bytes(source_dir: Path, archive_root: str = "") -> bytes:
    source_dir = source_dir.absolute()
    validate_safe_directory_tree(source_dir, "ZIP source tree")
    archive_root = archive_root.strip("/\\")
    archive_path = PurePosixPath(archive_root.replace("\\", "/"))
    if archive_root and (
        archive_path.is_absolute()
        or any(part in {"", ".", ".."} for part in archive_path.parts)
    ):
        raise ValueError(f"unsafe ZIP archive root: {archive_root!r}")
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(source_dir.rglob("*"), key=lambda item: item.relative_to(source_dir).as_posix()):
            if not path.is_file():
                continue
            if path.name == DISTRIBUTION_MANIFEST_NAME:
                continue
            rel = path.relative_to(source_dir).as_posix()
            if archive_root:
                rel = f"{archive_root}/{rel}"
            info = zipfile.ZipInfo(rel)
            info.date_time = (1980, 1, 1, 0, 0, 0)
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            zf.writestr(info, path.read_bytes())
    return buffer.getvalue()


def sync_directory_contents(
    source_dir: Path,
    mirror_root: Path,
    *,
    skip_names: set[str] | None = None,
    preserve_top_level_names: set[str] | None = None,
) -> int:
    source_dir = source_dir.absolute()
    mirror_root = mirror_root.absolute()
    validate_safe_directory_tree(source_dir, "sync source tree")
    validate_safe_directory_tree(mirror_root, "sync target tree", allow_missing=True)
    source_dir = source_dir.resolve()
    mirror_root = mirror_root.resolve()
    if source_dir != mirror_root and (
        source_dir in mirror_root.parents or mirror_root in source_dir.parents
    ):
        raise ValueError("sync source and target trees must not contain one another")
    skip_names = {name.lower() for name in (skip_names or set())}
    preserve_top_level_names = {name.lower() for name in (preserve_top_level_names or set())}

    def is_preserved(rel: Path) -> bool:
        return bool(rel.parts and rel.parts[0].lower() in preserve_top_level_names)

    if source_dir == mirror_root:
        return sum(
            1
            for path in source_dir.rglob("*")
            if path.is_file()
            and path.name.lower() not in skip_names
            and not is_preserved(path.relative_to(source_dir))
        )
    if mirror_root.exists() and not mirror_root.is_dir():
        raise NotADirectoryError(mirror_root)
    mirror_root.mkdir(parents=True, exist_ok=True)

    expected: set[str] = set()
    copied = 0
    for src in sorted(source_dir.rglob("*"), key=lambda item: item.relative_to(source_dir).as_posix()):
        rel = src.relative_to(source_dir)
        if is_preserved(rel):
            continue
        if not src.is_file():
            continue
        if src.name.lower() in skip_names:
            continue
        expected.add(rel.as_posix())
        copy_file_if_changed(src, mirror_root / rel)
        copied += 1

    for path in sorted(mirror_root.rglob("*"), key=lambda item: len(item.parts), reverse=True):
        rel_path = path.relative_to(mirror_root)
        if is_preserved(rel_path):
            continue
        rel = rel_path.as_posix()
        if path.is_file() and rel not in expected:
            path.unlink()
        elif path.is_dir():
            try:
                path.rmdir()
            except OSError:
                pass
    return copied


def read_distribution_manifest(project_root: Path) -> set[str]:
    manifest = project_root / DISTRIBUTION_MANIFEST_NAME
    if not manifest.exists():
        return set()
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return set()
    files = data.get("files", []) if isinstance(data, dict) else []
    return {str(item) for item in files if isinstance(item, str)}


def write_distribution_manifest(
    project_root: Path,
    expected: set[str],
    generated_at: str,
) -> None:
    data = {
        "version": 1,
        "generated_at": generated_at,
        "file_count": len(expected),
        "files": sorted(expected),
    }
    write_distribution_text(
        project_root / DISTRIBUTION_MANIFEST_NAME,
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
    )


def lake_manifest_for_distribution(package_name: str, mathlib_ref: str) -> str:
    ref = str(mathlib_ref or "").strip()
    if ref != "v4.27.0":
        return ""
    packages: list[dict[str, Any]] = [
        {
            "url": "https://github.com/leanprover-community/mathlib4",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "a3a10db0e9d66acbebf76c5e6a135066525ac900",
            "name": "mathlib",
            "manifestFile": "lake-manifest.json",
            "inputRev": "v4.27.0",
            "inherited": False,
            "configFile": "lakefile.lean",
        },
        {
            "url": "https://github.com/leanprover-community/plausible",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "009dc1e6f2feb2c96c081537d80a0905b2c6498f",
            "name": "plausible",
            "manifestFile": "lake-manifest.json",
            "inputRev": "main",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
        {
            "url": "https://github.com/leanprover-community/LeanSearchClient",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "5ce7f0a355f522a952a3d678d696bd563bb4fd28",
            "name": "LeanSearchClient",
            "manifestFile": "lake-manifest.json",
            "inputRev": "main",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
        {
            "url": "https://github.com/leanprover-community/import-graph",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "8f497d55985a189cea8020d9dc51260af1e41ad2",
            "name": "importGraph",
            "manifestFile": "lake-manifest.json",
            "inputRev": "main",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
        {
            "url": "https://github.com/leanprover-community/ProofWidgets4",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "c04225ee7c0585effbd933662b3151f01b600e40",
            "name": "proofwidgets",
            "manifestFile": "lake-manifest.json",
            "inputRev": "v0.0.85",
            "inherited": True,
            "configFile": "lakefile.lean",
        },
        {
            "url": "https://github.com/leanprover-community/aesop",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "cb837cc26236ada03c81837bebe0acd9c70ced7d",
            "name": "aesop",
            "manifestFile": "lake-manifest.json",
            "inputRev": "master",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
        {
            "url": "https://github.com/leanprover-community/quote4",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "bd58c9efe2086d56ca361807014141a860ddbf8c",
            "name": "Qq",
            "manifestFile": "lake-manifest.json",
            "inputRev": "master",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
        {
            "url": "https://github.com/leanprover-community/batteries",
            "type": "git",
            "subDir": None,
            "scope": "leanprover-community",
            "rev": "b25b36a7caf8e237e7d1e6121543078a06777c8a",
            "name": "batteries",
            "manifestFile": "lake-manifest.json",
            "inputRev": "main",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
        {
            "url": "https://github.com/leanprover/lean4-cli",
            "type": "git",
            "subDir": None,
            "scope": "leanprover",
            "rev": "55c37290ff6186e2e965d68cf853a57c0702db82",
            "name": "Cli",
            "manifestFile": "lake-manifest.json",
            "inputRev": "v4.27.0",
            "inherited": True,
            "configFile": "lakefile.toml",
        },
    ]
    data = {
        "version": "1.1.0",
        "packagesDir": ".lake/packages",
        "packages": packages,
        "name": package_name,
        "lakeDir": ".lake",
    }
    return json.dumps(data, ensure_ascii=False, indent=1) + "\n"


def render_distribution_readme(
    package_name: str,
    title: str,
    version: str,
    commit: str,
    github_repo: str,
    source_ref: str,
    generated_at: str,
    toolchain: str,
    mathlib_ref: str,
    module_names: list[str],
    lean_file_count: int,
    top_modules: list[str],
    locked_dependencies: bool,
) -> str:
    repo_line = f"- Source repository: {normalize_github_repo(github_repo)}\n" if github_repo else ""
    version_line = f"- Version: {version}\n" if version else ""
    commit_line = f"- Commit: {commit}\n" if commit else ""
    ref_line = f"- Source ref: {source_ref}\n" if source_ref else ""
    sample_import = module_names[0] if module_names else package_name
    generated_line = generated_at or "not recorded"
    top_module_block = "\n".join(f"- `{name}`" for name in top_modules)
    lock_note = "included" if locked_dependencies else "not included; run `lake update` before building"
    return f"""# {title}

This ZIP is a Lake project generated from the Lean sources used by the website.
The source tree follows the same shape as the working Lean project: Lake files at
the project root, and Lean source modules under `Lean4/`.

## Documentation

The generated ProCGroups documentation is available at:

{DEFAULT_DOCUMENTATION_URL}

## Build

For a fresh checkout or extracted ZIP:

```bash
lake exe cache get
lake build
```

If dependency download was interrupted, remove `.lake/` and run:

```bash
lake update
lake exe cache get
lake build
```

## Package Information

- Generated at: {generated_line}
- Package: {package_name}
- Lean toolchain: `{toolchain}`
- Mathlib ref: `{mathlib_ref}`
- Locked dependencies: {lock_note}
- Lean source files: {lean_file_count}
- Importable modules: {len(module_names)}
{repo_line}{ref_line}{version_line}{commit_line}

## Top-Level Libraries

{top_module_block}

## Use

```lean
import {sample_import}
```

The project root module is:

```lean
import {package_name}
```

The stable root includes the axiom-free, conditional `FenchelNielsenZomorrodian` API. It excludes
only `FenchelNielsenZomorrodian.WithAxioms` and the paper application; those remain available
through explicit opt-in roots:

```lean
import {package_name}Experimental
import {package_name}Papers
-- or, deliberately:
import {package_name}All
```
"""


def write_lean_distribution_project(
    lean_root: Path,
    project_root: Path,
    *,
    package_name: str,
    toolchain: str,
    mathlib_ref: str,
    title: str,
    version: str,
    commit: str,
    github_repo: str,
    source_ref: str,
    generated_at: str,
) -> list[str]:
    project_root = project_root.resolve()
    project_root.mkdir(parents=True, exist_ok=True)
    source_dir = project_root / "Lean4"
    source_dir.mkdir(parents=True, exist_ok=True)

    lean_files = lean_distribution_files(lean_root)
    module_names = sorted({module_name_from_path(path, lean_root) for path in lean_files})
    existing_modules = set(module_names)
    top_modules = sorted({top_level_module_from_relative_path(path.relative_to(lean_root)) for path in lean_files})
    previous = read_distribution_manifest(project_root)
    expected: set[str] = {DISTRIBUTION_MANIFEST_NAME}

    for src in lean_files:
        rel = src.relative_to(lean_root)
        expected.add((Path("Lean4") / rel).as_posix())
        copy_file_if_changed(src, source_dir / rel)

    for top in top_modules:
        if top in existing_modules:
            continue
        child_imports = [name for name in module_names if name.startswith(top + ".")]
        if child_imports:
            expected.add(f"Lean4/{top}.lean")
            write_distribution_text(source_dir / f"{top}.lean", "\n".join(f"import {name}" for name in child_imports) + "\n")
            module_names.append(top)

    module_names = sorted(set(module_names))
    experimental_modules = [
        name for name in module_names if name == "FenchelNielsenZomorrodian.WithAxioms"
    ]
    paper_modules = [
        name for name in top_modules if name == "Yama2026_Sections_1_And_2_1"
    ]
    stable_modules = [
        name for name in top_modules
        if name not in set(paper_modules)
    ]
    root_imports = "\n".join(f"import {name}" for name in stable_modules)
    expected.add(f"{package_name}.lean")
    write_distribution_text(project_root / f"{package_name}.lean", root_imports + "\n")

    experimental_root = f"{package_name}Experimental"
    papers_root = f"{package_name}Papers"
    all_root = f"{package_name}All"
    expected.update({f"{experimental_root}.lean", f"{papers_root}.lean", f"{all_root}.lean"})
    write_distribution_text(
        project_root / f"{experimental_root}.lean",
        "\n".join(f"import {name}" for name in experimental_modules) + "\n",
    )
    write_distribution_text(
        project_root / f"{papers_root}.lean",
        "\n".join(f"import {name}" for name in paper_modules) + "\n",
    )
    write_distribution_text(
        project_root / f"{all_root}.lean",
        f"import {package_name}\nimport {experimental_root}\nimport {papers_root}\n",
    )

    mathlib_ref = str(mathlib_ref or "master").strip() or "master"
    default_targets = ",\n".join(f'  "{name}"' for name in [package_name, *stable_modules])
    lean_libs = "\n\n".join(
        f'[[lean_lib]]\nname = "{name}"\nsrcDir = "Lean4"' for name in top_modules
    )
    aggregate_lean_libs = "\n\n".join(
        f'[[lean_lib]]\nname = "{name}"'
        for name in (experimental_root, papers_root, all_root)
    )
    lakefile = f"""enableArtifactCache = true
restoreAllArtifacts = true

name = "{package_name}"
version = "0.1.0-dev"
keywords = ["math"]
defaultTargets = [
{default_targets}
]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{mathlib_ref}"

[[lean_lib]]
name = "{package_name}"

{lean_libs}

{aggregate_lean_libs}
"""
    expected.update({
        "lakefile.toml",
        "lean-toolchain",
        "README.md",
        ".gitignore",
        ".gitattributes",
        "AXIOMS.md",
        AXIOM_MANIFEST_NAME,
        "tools/check_axiom_manifest.py",
        "tools/check_generated_site.py",
    })
    write_distribution_text(project_root / "lakefile.toml", lakefile)
    write_distribution_text(project_root / "lean-toolchain", toolchain.strip() + "\n")
    lock_text = lake_manifest_for_distribution(package_name, mathlib_ref)
    if lock_text:
        expected.add("lake-manifest.json")
        write_distribution_text(project_root / "lake-manifest.json", lock_text)
    write_distribution_text(
        project_root / ".gitignore",
        ".lake/\n.lake\nbuild/\n*.olean\n*.ilean\n*.trace\n.DS_Store\nThumbs.db\n",
    )
    write_distribution_text(
        project_root / ".gitattributes",
        "* text=auto eol=lf\n*.bat text eol=crlf\n",
    )
    checker_source = Path(__file__).resolve().parent / "tools" / "check_generated_site.py"
    write_distribution_text(
        project_root / "tools" / "check_generated_site.py",
        checker_source.read_text(encoding="utf-8"),
    )
    axiom_checker_source = Path(__file__).resolve().parent / "tools" / "check_axiom_manifest.py"
    write_distribution_text(
        project_root / "tools" / "check_axiom_manifest.py",
        axiom_checker_source.read_text(encoding="utf-8"),
    )
    axiom_rows: list[dict[str, Any]] = []
    allowed_axioms = {
        ("FenchelNielsenZomorrodian.WithAxioms", "finiteSubgroup_le_conj_ellipticStabilizer"),
        ("FenchelNielsenZomorrodian.WithAxioms", "finiteSubgroup_le_conj_inertia"),
    }
    for source in lean_files:
        module = module_name_from_path(source, lean_root)
        source_lines = source.read_text(encoding="utf-8").splitlines()
        for line_number, line in enumerate(
            stripped_code_lines_for_parsing(source_lines), 1
        ):
            match = AXIOM_COMMAND_RE.match(line)
            if not match:
                continue
            name = match.group(1).strip("`")
            if (module, name) not in allowed_axioms:
                raise ValueError(
                    f"unapproved project-local axiom: {module}.{name} ({source}:{line_number})"
                )
            axiom_rows.append({
                "module": module,
                "name": name,
                "path": source.relative_to(lean_root).as_posix(),
                "line": line_number,
                "boundary": "opt-in",
            })
    axiom_rows.sort(key=lambda row: (row["module"], row["name"], row["line"]))
    axiom_manifest = {
        "schemaVersion": 1,
        "sourceCommit": commit,
        "stableRoot": package_name,
        "stableModules": stable_modules,
        "optInRoots": [experimental_root, papers_root, all_root],
        "optInModules": experimental_modules,
        "paperModules": paper_modules,
        "projectLocalAxioms": axiom_rows,
    }
    write_distribution_text(
        project_root / AXIOM_MANIFEST_NAME,
        json.dumps(axiom_manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
    )
    axiom_table = "\n".join(
        f'| `{row["name"]}` | `{row["module"]}` | '
        f'[`{row["path"]}:{row["line"]}`](Lean4/{row["path"]}#L{row["line"]}) | opt-in |'
        for row in axiom_rows
    ) or "| _none_ | — | — | — |"
    write_distribution_text(
        project_root / "AXIOMS.md",
        f"""# Project-local axiom manifest

Source commit: `{commit}`

The default `{package_name}` root imports no project-local axiom.  The declarations below are
reachable only through `{experimental_root}` (and consequently `{all_root}`).

| Declaration | Module | Source | Boundary |
|---|---|---|---|
{axiom_table}

This file and `{AXIOM_MANIFEST_NAME}` are generated from the Lean source.  CI checks them for
drift; neither file claims that Mathlib itself is axiom-free.
""",
    )
    write_distribution_text(
        project_root / "README.md",
        render_distribution_readme(
            package_name,
            title,
            version,
            commit,
            github_repo,
            source_ref,
            generated_at,
            toolchain,
            mathlib_ref,
            module_names,
            len(lean_files),
            top_modules,
            bool(lock_text),
        ),
    )
    for rel in sorted(previous - expected, key=lambda item: item.count("/"), reverse=True):
        path = project_root / rel
        if path.is_file() and path.relative_to(project_root).as_posix() not in expected:
            path.unlink()
    for path in sorted(project_root.rglob("*"), key=lambda item: len(item.parts), reverse=True):
        if path.is_dir():
            try:
                path.rmdir()
            except OSError:
                pass
    write_distribution_manifest(project_root, expected, generated_at)
    return module_names


def build_lean_distribution_zip(
    lean_root: Path,
    project_root: Path,
    zip_path: Path,
    *,
    package_name: str,
    toolchain: str,
    mathlib_ref: str,
    title: str,
    version: str,
    commit: str,
    github_repo: str,
    source_ref: str,
    generated_at: str,
    out_root: Path,
    generated: set[str],
    stats: WriteStats,
    source_mirror_root: Path | None = None,
    reporter: BuildReporter | None = None,
) -> list[str]:
    module_names = write_lean_distribution_project(
        lean_root,
        project_root,
        package_name=package_name,
        toolchain=toolchain,
        mathlib_ref=mathlib_ref,
        title=title,
        version=version,
        commit=commit,
        github_repo=github_repo,
        source_ref=source_ref,
        generated_at=generated_at,
    )
    if source_mirror_root is not None:
        preserve_names = set(REPOSITORY_METADATA_NAMES)
        try:
            relative_output = out_root.resolve().relative_to(source_mirror_root.resolve())
            if relative_output.parts:
                preserve_names.add(relative_output.parts[0])
        except ValueError:
            pass
        mirrored = sync_directory_contents(
            project_root,
            source_mirror_root,
            skip_names={DISTRIBUTION_MANIFEST_NAME},
            preserve_top_level_names=preserve_names,
        )
        if reporter:
            reporter.progress(f"Lean distribution mirror synced: {source_mirror_root} ({mirrored} file(s))")
    zip_data = zip_directory_bytes(project_root, archive_root=project_root.name)
    changed = write_binary_file(zip_path, zip_data, out_root=out_root, generated=generated, stats=stats)
    if reporter:
        state = "updated" if changed else "unchanged"
        reporter.progress(f"Lean distribution ZIP {state}: {zip_path.name} ({len(module_names)} module import(s))")
    return module_names


def remove_distribution_workdir(path: Path, stats: WriteStats | None = None) -> bool:
    if not path.exists():
        return False
    if not path.is_dir():
        return False
    manifest = path / DISTRIBUTION_MANIFEST_NAME
    if not manifest.exists():
        return False
    remove_generated_path(path, stats)
    return True


def cleanup_distribution_workdirs(repo_root: Path, package_name: str, stats: WriteStats | None = None, reporter: BuildReporter | None = None) -> None:
    dist_root = repo_root / "dist"
    candidates = [
        dist_root / package_name,
        dist_root / "lean-project",
    ]
    removed = 0
    for path in candidates:
        if remove_distribution_workdir(path, stats):
            removed += 1
            if reporter:
                reporter.progress(f"Removed obsolete generated workdir: {path}")
    try:
        dist_root.rmdir()
        removed += 1
        if reporter:
            reporter.progress(f"Removed empty generated directory: {dist_root}")
    except OSError:
        pass
    if reporter and not removed:
        reporter.progress("No obsolete Lean distribution workdirs found")


def should_skip_component_lean_path(path: Path, component_dir: Path) -> bool:
    """Return whether a file under an explicitly selected component is generated noise."""
    rel = path.relative_to(component_dir)
    if rel.name in SKIP_LEAN_FILES:
        return True
    return any(part.startswith('.') or part in SKIP_LEAN_DIRS for part in rel.parts)


def component_lean_sources(
    source_root: Path,
    component_dirs: Iterable[Path],
) -> list[tuple[Path, Path, str]]:
    """Return source path, module root, and public component triples.

    Module names are relative to each component directory, while a module's
    public source path remains relative to ``source_root``.  Component names
    are supplied by the caller instead of being built into the generator.
    """
    source_root = source_root.resolve()
    if source_root.is_symlink() or not source_root.is_dir():
        raise ValueError(f"Lean source root must be a real directory: {source_root}")

    roots: list[tuple[Path, str]] = []
    seen_roots: set[Path] = set()
    seen_components: set[str] = set()
    for raw_component_dir in component_dirs:
        component_dir = Path(raw_component_dir).resolve()
        if component_dir in seen_roots:
            raise ValueError(f"duplicate Lean component directory: {component_dir}")
        seen_roots.add(component_dir)
        if component_dir.is_symlink() or not component_dir.is_dir():
            raise ValueError(
                f"Lean component directory must be a real directory: {component_dir}"
            )
        try:
            relative_component = component_dir.relative_to(source_root)
        except ValueError as error:
            raise ValueError(
                f"Lean component directory must be inside {source_root}: {component_dir}"
            ) from error
        if relative_component == Path("."):
            raise ValueError(
                "Lean component directory must be below the source root, "
                f"not the source root itself: {component_dir}"
            )
        if len(relative_component.parts) != 1:
            raise ValueError(
                "Lean component directory must be a direct child of the source "
                f"root: {component_dir}"
            )
        component = relative_component.name
        if component in seen_components:
            raise ValueError(f"duplicate Lean component name: {component}")
        seen_components.add(component)
        roots.append((component_dir, component))

    sources: list[tuple[Path, Path, str]] = []
    modules_seen: dict[str, Path] = {}
    source_paths_seen: set[str] = set()
    for component_dir, component in roots:
        for path in sorted(component_dir.rglob("*.lean")):
            if should_skip_component_lean_path(path, component_dir):
                continue
            if path.is_symlink() or not path.is_file():
                raise ValueError(f"Lean component contains an unsafe source: {path}")
            module = module_name_from_path(path, component_dir)
            previous = modules_seen.get(module)
            if previous is not None:
                raise ValueError(
                    f"duplicate Lean module name {module!r}: {previous} and {path}"
                )
            modules_seen[module] = path
            source_path = path.relative_to(source_root).as_posix()
            if source_path in source_paths_seen:
                raise ValueError(f"duplicate Lean source path: {source_path}")
            source_paths_seen.add(source_path)
            sources.append((path, component_dir, component))
    return sources


def prepare_modules(
    lean_root: Path | None,
    *,
    component_dirs: Iterable[Path] | None = None,
    module_components: dict[str, str] | None = None,
    source_root: Path | None = None,
    fixed_updated_at: int = 0,
) -> tuple[list[Module], dict[str, Declaration]]:
    if lean_root is None and source_root is None:
        raise ValueError("lean_root or source_root is required")
    effective_source_root = Path(source_root or lean_root).resolve()
    if component_dirs is not None and module_components is not None:
        raise ValueError("component_dirs and module_components are mutually exclusive")

    if component_dirs is None:
        module_root = Path(lean_root or effective_source_root).resolve()
        if module_components is not None:
            lean_sources = []
            for module_name in sorted(module_components):
                path = module_root.joinpath(*module_name.split(".")).with_suffix(".lean")
                if path.is_symlink() or not path.is_file():
                    raise ValueError(
                        f"configured Lean module is missing or unsafe: "
                        f"{module_name} ({path})"
                    )
                try:
                    if path.resolve().relative_to(module_root) == Path("."):
                        raise ValueError
                except ValueError as error:
                    raise ValueError(
                        f"configured Lean module escapes the source root: {path}"
                    ) from error
                lean_sources.append((path, module_root, ""))
        else:
            lean_sources = [
                (path, module_root, "")
                for path in sorted(module_root.rglob("*.lean"))
                if not should_skip_lean_path(path, module_root)
            ]
    else:
        lean_sources = component_lean_sources(effective_source_root, component_dirs)

    modules: list[Module] = []
    for path, module_root, storage_component in lean_sources:
        module_name = module_name_from_path(path, module_root)
        if module_components is not None:
            component = module_components.get(module_name, "")
            if not component:
                raise ValueError(
                    f"no public library is configured for Lean module {module_name}"
                )
            source_component_prefix: bool | None = None
        else:
            component = storage_component
            source_component_prefix = True if component_dirs is not None else None
        modules.append(
            parse_lean_file(
                path,
                module_root,
                source_root=effective_source_root,
                component=component,
                source_component_prefix=source_component_prefix,
            )
        )
    if module_components is not None:
        discovered = {module.name for module in modules}
        extra = sorted(set(module_components) - discovered)
        if extra:
            raise ValueError(
                "public-library mapping contains missing Lean modules: "
                + ", ".join(extra[:10])
            )
    modules.sort(key=lambda module: module.name)
    module_by_name = {m.name: m for m in modules}
    imported_by: dict[str, list[str]] = defaultdict(list)
    git_timestamps = {} if fixed_updated_at else git_updated_at_map(
        effective_source_root, [m.rel_path for m in modules]
    )
    for m in modules:
        m.updated_at = fixed_updated_at or git_timestamps.get(m.rel_path) or file_mtime(
            effective_source_root, m.rel_path
        )
        m.updated_label = timestamp_label(m.updated_at)
        for imp in m.imports:
            if imp in module_by_name:
                imported_by[imp].append(m.name)
    for m in modules:
        m.imported_by = sorted(imported_by[m.name])
        m.natural = module_doc_natural_entry(m.module_doc)
        for d in m.decls:
            d.natural = declaration_doc_natural_entry(d.doc)
    return modules, declaration_lookup(modules)


def render_child_cards(modules: list[Module], parent_name: str, root: str, show_nested_samples: bool = True) -> str:
    modules_by_name = {module.name: module for module in modules}
    sections = []
    for child, child_modules in group_modules_by_direct_child(modules, parent_name).items():
        anchor = child_anchor_module(parent_name, child, child_modules)
        content_modules = [module for module in child_modules if not is_wrapper_module(module)]
        decls = [decl for module in content_modules for decl in module.decls]
        note_source = anchor or next((module for module in content_modules if module_card_note(module, modules_by_name)), None) or child_modules[0]
        note = truncate_text(child_group_note(note_source, child_modules, modules_by_name, root), 180)
        updated_at = max((module.updated_at for module in child_modules), default=0)
        target_module = anchor or note_source
        heading = (
            f'<a href="{escape(root + module_html_path(target_module.name, target_module.component))}">'
            f"{escape(child)}</a>"
        )
        sample_html = ""
        if show_nested_samples and not note:
            sample_targets = content_modules[:6]
            sample_links = ", ".join(
                f'<a href="{escape(root + module_html_path(module.name, module.component))}">{escape(relative_module_name(module.name, parent_name))}</a>'
                for module in sample_targets
            )
            more = len(content_modules) - len(sample_targets)
            if sample_links:
                if more > 0:
                    sample_links += f", and {more} more"
                sample_html = f'<div class="sample library-files">{sample_links}</div>'
        meta = (
            f"{count_label(len(child_modules), 'file')} | "
            f"{count_label(len(decls), 'declaration')}"
        )
        summary = kind_summary(decls)
        if summary != "No declarations":
            meta += f" | {summary}"
        sections.append(f'''<section class="module-row library-row" data-sort-item data-order="{len(sections)}" data-name="{escape(child)}" data-updated="{updated_at}" data-files="{len(child_modules)}" data-decls="{len(decls)}" data-theorems="{count_decls(decls, {"theorem", "lemma"})}">
  <h2>{heading}</h2>
  <div class="meta">{escape(meta)}</div>
  {sample_html}
  {f'<div class="sample tex2jax_process">{escape(note)}</div>' if note else ''}
</section>''')
    return "\n".join(sections) if sections else '<div class="empty">No files.</div>'


def render_module_page(
    module: Module,
    modules: list[Module],
    by_token: dict[str, Declaration],
    title: str,
    source_base_url: str = "",
    module_names: set[str] | None = None,
    link_map_cache: dict[str, dict[str, str]] | None = None,
    documentation_url: str = "",
) -> str:
    out_path = module_html_path(module.name, module.component)
    root = root_prefix_for(out_path)
    links = cached_link_map_for(by_token, root, link_map_cache)
    module_names = module_names or {m.name for m in modules}
    module_components = {item.name: item.component for item in modules}
    import_only = is_wrapper_module(module)
    has_descendants = any(
        item.name.startswith(module.name + ".") for item in modules
    )
    if not module.decls and has_descendants:
        return render_wrapper_module_page(
            module,
            modules,
            module_names,
            title,
            source_base_url,
            documentation_url,
        )
    modules_by_name = {item.name: item for item in modules}
    source_file_url = source_base_url.rstrip('/') + '/' + module.rel_path if source_base_url else ''
    info_blocks = "\n".join([
        render_module_imports(
            module,
            module_names,
            root,
            module_components,
            expanded=import_only,
        ),
        render_imported_by(module, root, module_components),
    ])
    overview = render_module_overview(
        module,
        modules_by_name,
    )
    if module.decls:
        module_meta = kind_summary(module.decls)
        has_rendered_proofs = any(
            is_proof_kind(declaration.kind)
            and bool(lean_parts_for_decl(declaration)[1].strip())
            for declaration in module.decls
        )
        proof_toggle = (
            '<button id="toggle_all_proofs" class="proof-toggle-all" '
            'type="button">Show all Lean proofs</button>'
            if has_rendered_proofs
            else ""
        )
        declarations = (
            '<section class="decl-toolbar"><h2>Declarations</h2>'
            + proof_toggle
            + "</section>\n"
            '<div class="decl-list">'
            + "\n".join(
                render_decl(d, root, links, source_base_url) for d in module.decls
            )
            + '</div>'
        )
    else:
        import_label = "import" if len(module.imports) == 1 else "imports"
        module_meta = (
            f"{len(module.imports)} {import_label} | import-only module | "
            "0 declarations"
            if import_only
            else "No declarations"
        )
        empty_message = (
            "This import-only module declares no new names."
            if import_only
            else "No declarations."
        )
        declarations = (
            '<section class="decl-toolbar"><h2>Declarations</h2></section>'
            f'<div class="decl-list"><div class="empty">{empty_message}</div></div>'
        )
    content = f'''<section class="module-head">
  <div class="module-head-top">
    <div>
      {render_module_breadcrumb(module.name, module_names, root, module_components=module_components)}
      <h1 class="module-title">{escape(module.name)}</h1>
      <div class="module-meta">{escape(module_meta)}</div>
      {overview}
      {f'<div class="meta"><a href="{escape(source_file_url)}">Open this file on GitHub</a></div>' if source_file_url else ''}
    </div>
  </div>
  {info_blocks}
</section>
{declarations}'''
    return full_page(
        f"{module.name} | {title}",
        root,
        shell(content, module.name),
        label=module.name,
        site_title=title,
        description=(
            truncate_text(module_overview_text(module, modules_by_name), 220)
            or f"Lean 4 API documentation for {module.name}."
        ),
        canonical_url=(
            documentation_url.rstrip("/") + "/" + out_path
            if documentation_url
            else ""
        ),
        render_math=True,
    )


def render_wrapper_module_page(
    module: Module,
    modules: list[Module],
    module_names: set[str],
    title: str,
    source_base_url: str = "",
    documentation_url: str = "",
) -> str:
    out_path = module_html_path(module.name, module.component)
    root = root_prefix_for(out_path)
    descendants = [m for m in modules if m.name == module.name or m.name.startswith(module.name + '.')]
    child_groups = group_modules_by_direct_child(descendants, module.name)
    child_modules = [child for group in child_groups.values() for child in group]
    decls = [d for m in child_modules if not is_wrapper_module(m) for d in m.decls]
    modules_by_name = {item.name: item for item in modules}
    module_components = {item.name: item.component for item in modules}
    overview = render_module_overview(module, modules_by_name)
    info_blocks = "\n".join(
        [
            render_module_imports(
                module,
                module_names,
                root,
                module_components,
            ),
            render_imported_by(module, root, module_components),
        ]
    )
    source_file_url = (
        source_base_url.rstrip("/") + "/" + module.rel_path
        if source_base_url
        else ""
    )
    content = f'''<section class="module-head">
  <div class="module-head-top">
    <div>
      {render_module_breadcrumb(module.name, module_names, root, module_components=module_components)}
      <h1 class="module-title">{escape(module.name)}</h1>
      <div class="module-meta">{count_label(len(child_groups), "section")} | {count_label(len(child_modules), "file")} | {count_label(len(decls), "declaration")}</div>
      {overview}
      {f'<div class="meta"><a href="{escape(source_file_url)}">Open this file on GitHub</a></div>' if source_file_url else ''}
    </div>
  </div>
  {info_blocks}
</section>
<section>
  <div id="topic_list" class="module-list">{render_child_cards(descendants, module.name, root, show_nested_samples=False)}</div>
</section>'''
    return full_page(
        f"{module.name} | {title}",
        root,
        shell(content, module.name),
        label=module.name,
        site_title=title,
        description=(
            truncate_text(module_overview_text(module, modules_by_name), 220)
            or f"Lean 4 module index for {module.name}."
        ),
        canonical_url=(
            documentation_url.rstrip("/") + "/" + out_path
            if documentation_url
            else ""
        ),
        render_math=True,
    )


def render_source_page(
    module: Module,
    by_token: dict[str, Declaration],
    title: str,
    module_names: set[str] | None = None,
    module_components: dict[str, str] | None = None,
    link_map_cache: dict[str, dict[str, str]] | None = None,
    documentation_url: str = "",
) -> str:
    out_path = source_html_path(
        module.rel_path,
        module.component,
        module.source_component_prefix,
    )
    root = root_prefix_for(out_path)
    links = cached_link_map_for(by_token, root, link_map_cache)
    module_names = set(module_names or {decl.module for decl in by_token.values()})
    rows = []
    source_lines = module.source.splitlines()
    highlighted_lines = (
        highlight_lean(module.source, links).split("\n") if source_lines else []
    )
    if len(highlighted_lines) != len(source_lines):
        raise ValueError(
            f"source highlighting changed line count for {module.rel_path}: "
            f"{len(source_lines)} -> {len(highlighted_lines)}"
        )
    for i, highlighted_line in enumerate(highlighted_lines, start=1):
        rows.append(f'<div class="src-line" id="L{i}"><a class="lineno" href="#L{i}">{i}</a><span class="linecode">{highlighted_line}</span></div>')
    content = f'''<section class="module-head">
  <div class="module-head-top">
    <div>
      {render_module_breadcrumb(module.name, module_names, root, source=True, module_components=module_components)}
      <h1 class="module-title">Source: {escape(module.name)}</h1>
    </div>
  </div>
</section>
<div class="source-box">{"".join(rows)}</div>'''
    source_label = f"Source: {module.name}"
    return full_page(
        f"{source_label} | {title}",
        root,
        shell(content, module.name),
        label=source_label,
        body_class="source-page",
        site_title=title,
        description=f"Lean 4 source listing for {module.name}.",
        canonical_url=(
            documentation_url.rstrip("/") + "/" + out_path
            if documentation_url
            else ""
        ),
    )


def render_index(
    modules: list[Module],
    title: str,
    github_repo: str = "",
    documentation_url: str = DEFAULT_DOCUMENTATION_URL,
    component_display_names: dict[str, str] | None = None,
) -> str:
    content_modules = [m for m in modules if not is_wrapper_module(m)]
    total = sum(len(m.decls) for m in content_modules)
    grouped = group_modules_by_library(modules)
    modules_by_name = {module.name: module for module in modules}
    display_names = dict(component_display_names or {})
    sections = []
    for lib, library_modules in grouped.items():
        display_name = display_names.get(lib, lib)
        top_level_groups = group_modules_by_direct_child(library_modules, lib)
        if not top_level_groups:
            continue
        library_content_modules = [m for m in library_modules if not is_wrapper_module(m)]
        library_decls = [d for m in library_content_modules for d in m.decls]
        axiom_count = count_decls(library_decls, {"axiom"})
        sorry_count = sum(count_sorry_tokens(m.source) for m in library_content_modules)
        frontier_bits: list[str] = []
        if sorry_count:
            frontier_bits.append(f'{sorry_count} <code>sorry</code>')
        if axiom_count:
            frontier_bits.append(f'{axiom_count} <code>axiom</code>')
        wrapper = next((m for m in library_modules if m.name == lib), None)
        top_level_modules = [child for group in top_level_groups.values() for child in group]
        note_source = wrapper or top_level_modules[0]
        note = module_card_note(note_source, modules_by_name)
        note_html = strip_paragraph_wrapper(simple_markdown(note))
        updated_at = max((m.updated_at for m in top_level_modules), default=0)
        heading = (
            f'<a href="{escape(module_html_path(wrapper.name, wrapper.component))}">{escape(display_name)}</a>'
            if wrapper
            else escape(display_name)
        )
        meta = (
            f"{count_label(len(top_level_groups), 'top-level group')} | "
            f"{count_label(len(library_content_modules), 'file')} | "
            f"{count_label(len(library_decls), 'declaration')}"
        )
        if frontier_bits:
            meta += " | " + " | ".join(frontier_bits)
        sections.append(f'''<section id="library-{escape(lib)}" class="module-head" data-sort-item data-order="{len(sections)}" data-name="{escape(display_name)}" data-updated="{updated_at}" data-files="{len(top_level_groups)}" data-decls="{len(library_decls)}" data-theorems="{count_decls(library_decls, {"theorem", "lemma"})}">
  <div class="module-head-top">
    <div>
      <div class="eyebrow">Library</div>
      <h2 class="module-title">{heading}</h2>
      <div class="module-meta">{meta}</div>
      {f'<div class="sample tex2jax_process">{note_html}</div>' if note_html else ''}
    </div>
  </div>
</section>''')
    repo_note = f'<p class="meta"><a href="{escape(github_repo)}">GitHub repository</a> for the Lean source package.</p>' if github_repo else ''
    content = f'''<section>
  <h1 class="page-title">{escape(title)}</h1>
  <p>{escape(DOCUMENTATION_DESCRIPTION)}</p>
  <div class="stats"><span>{count_label(len(grouped), "library", "libraries")}</span><span>{count_label(len(content_modules), "file")}</span><span>{count_label(total, "declaration")}</span></div>
  {repo_note}
</section>
<section class="sort-bar" aria-label="Sort libraries">
  <label>Sort <select data-sort-target="library_list">
    <option value="updated">Recently updated</option>
    <option value="name">Name</option>
    <option value="decls">Declarations</option>
    <option value="files">Files</option>
    <option value="theorems">Theorems and lemmas</option>
  </select></label>
  <label>Order <select data-sort-direction-target="library_list">
    <option value="desc">Descending</option>
    <option value="asc">Ascending</option>
  </select></label>
</section>
<div id="library_list">{"\n".join(sections)}</div>'''
    return full_page(
        title,
        './',
        shell(content),
        site_title=title,
        description=DOCUMENTATION_DESCRIPTION,
        canonical_url=documentation_url,
        render_math=True,
    )


def render_find_page(
    title: str,
    documentation_url: str = DEFAULT_DOCUMENTATION_URL,
) -> str:
    out_path = 'find/index.html'
    root = root_prefix_for(out_path)
    content = '''<section>
  <h1 class="page-title">Search Results</h1>
</section>
<section id="search_results" class="search-results tex2jax_process"></section>'''
    return full_page(
        f"Search | {title}",
        root,
        shell(content),
        label="Search Results",
        site_title=title,
        description=f"Search {title} modules, declarations, and statements.",
        canonical_url=documentation_url.rstrip("/") + "/find/",
        render_math=True,
        force_math=True,
    )




def build_tree_data(
    modules: list[Module],
    component_display_names: dict[str, str] | None = None,
) -> list[dict[str, Any]]:
    tree: dict[str, Any] = {}
    display_names = dict(component_display_names or {})
    for m in sorted(modules, key=lambda x: (x.component.lower(), x.name.lower())):
        node = tree.setdefault(m.component, {}) if m.component else tree
        module_parts = m.name.split(".")
        parts = (*module_parts[:-1], module_parts[-1] + ".lean")
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = {
            "n": parts[-1],
            "m": m.name,
            "u": module_html_path(m.name, m.component),
        }

    def convert(node: dict[str, Any], depth: int = 0) -> list[dict[str, Any]]:
        dirs = [(k, v) for k, v in node.items() if isinstance(v, dict) and "u" not in v]
        files = [(k, v) for k, v in node.items() if isinstance(v, dict) and "u" in v]
        out = []
        for name, child in sorted(dirs, key=lambda x: x[0].lower()):
            display_name = (
                display_names.get(name, name) if depth == 0 else name
            )
            out.append({"n": display_name, "c": convert(child, depth + 1)})
        for _name, file_node in sorted(files, key=lambda x: x[0].lower()):
            out.append(file_node)
        return out

    return convert(tree)


def normalize_github_repo(repo: str) -> str:
    repo = str(repo or '').strip().rstrip('/')
    if repo.endswith('.git'):
        repo = repo[:-4]
    return repo


def pinned_github_archive_url(repo: str, commit: str) -> str:
    """Return an immutable GitHub source archive URL for a full commit SHA."""
    repo = normalize_github_repo(repo)
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo):
        repo = "https://github.com/" + repo
    if not re.fullmatch(
        r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+",
        repo,
    ):
        raise ValueError(f"GitHub repository URL is required for archive mode: {repo!r}")
    commit = require_full_git_sha(commit, "GitHub archive commit")
    return f"{repo}/archive/{commit}.zip"


def github_source_base(repo: str, commit: str) -> str:
    repo = normalize_github_repo(repo)
    commit = require_full_git_sha(commit) if repo else ''
    return f'{repo}/blob/{commit}/Lean4/' if repo and commit else ''


def github_clone_url(repo: str) -> str:
    repo = normalize_github_repo(repo)
    if not repo:
        return ''
    if re.match(r'^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$', repo):
        repo = 'https://github.com/' + repo
    return repo + '.git' if repo.startswith('http') and not repo.endswith('.git') else repo


def clone_lean_repository(repo: str, ref: str, target: Path) -> None:
    clone_url = github_clone_url(repo)
    if not clone_url:
        raise ValueError('--lean-github-repo is empty.')
    subprocess.run(['git', 'clone', '--depth', '1', clone_url, str(target)], check=True)
    if ref:
        subprocess.run(['git', '-C', str(target), 'fetch', '--depth', '1', 'origin', ref], check=True)
        subprocess.run(['git', '-C', str(target), 'checkout', '--detach', 'FETCH_HEAD'], check=True)


def git_head_commit(root: Path) -> str:
    try:
        proc = subprocess.run(
            ['git', '-C', str(root), 'rev-parse', 'HEAD'],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=5,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return ''
    return proc.stdout.strip() if proc.returncode == 0 else ''


def require_full_git_sha(value: str, label: str = "commit") -> str:
    value = str(value or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ValueError(f"{label} must be a full 40-character Git SHA, not a branch name: {value!r}")
    return value


def git_commit_timestamp(root: Path, commit: str) -> str:
    """Return the immutable committer timestamp for an existing local commit."""
    commit = require_full_git_sha(commit)
    proc = subprocess.run(
        ["git", "-C", str(root), "show", "-s", "--format=%cI", commit],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=10,
        check=False,
    )
    if proc.returncode != 0 or not proc.stdout.strip():
        detail = proc.stderr.strip() or "commit is not present in the local mirror"
        raise ValueError(f"Cannot read timestamp for source commit {commit}: {detail}")
    return proc.stdout.strip()


def detect_lean_toolchain(lean_root: Path) -> str:
    candidates = [lean_root / 'lean-toolchain', lean_root.parent / 'lean-toolchain']
    for path in candidates:
        if path.exists():
            return path.read_text(encoding='utf-8').strip()
    return ''


def public_path_label(path: Path | None) -> str:
    if path is None:
        return ''
    resolved = path.resolve()
    try:
        return resolved.relative_to(Path(__file__).resolve().parent).as_posix()
    except ValueError:
        return resolved.name


def build_info_dict(
    title: str,
    version: str,
    commit: str,
    github_repo: str,
    lean_root: Path,
    generated_at: str = "",
    source_ref: str = "",
    lean_toolchain: str = "",
    libraries: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    return {
        'siteTitle': title,
        'version': version or '',
        'commit': commit or '',
        'sourceRef': source_ref or '',
        'sourceRepository': normalize_github_repo(github_repo),
        'leanToolchain': lean_toolchain or detect_lean_toolchain(lean_root),
        'generatedAt': generated_at or '',
        'leanRoot': public_path_label(lean_root),
        'documentationSource': "Lean doc comments",
        'libraries': list(libraries or []),
    }


def render_download_page(
    title: str,
    version: str,
    commit: str,
    github_repo: str,
    source_ref: str = "",
    zip_name: str = DEFAULT_LEAN_ZIP_NAME,
    package_name: str = DEFAULT_LEAN_PACKAGE_NAME,
    download_url: str = "",
) -> str:
    out_path = 'download/index.html'
    root = root_prefix_for(out_path)
    repo = normalize_github_repo(github_repo)
    ref = commit or source_ref or version
    zip_name = Path(zip_name or DEFAULT_LEAN_ZIP_NAME).name
    package_name = lean_package_name(package_name)
    github_button = (
        f'<a class="action-button secondary" href="{escape(repo)}" target="_blank" rel="noopener">GitHub repository</a>'
        if repo else '<span class="action-button disabled" aria-disabled="true">GitHub link not configured</span>'
    )
    meta_parts = [package_name]
    if version:
        meta_parts.append(version)
    if ref:
        meta_parts.append(ref[:12] if len(ref) > 12 else ref)
    download_href = download_url or zip_name
    download_label = "Download source archive" if download_url else "Download ZIP"
    download_note = (
        f'This source archive is pinned to commit <code>{escape(commit)}</code>.'
        if download_url
        else (
            "After extracting the ZIP, run <code>lake update</code> and "
            "<code>lake build</code>."
        )
    )
    content = f'''<section class="download-hero">
  <h1 class="page-title">Download</h1>
  <div class="meta">{escape(' · '.join(meta_parts))}</div>
  <p>Download the generated Lake project for the Lean sources used on this site.</p>
  <div class="download-actions">
    <a class="action-button primary" href="{escape(download_href)}">{download_label}</a>
    {github_button}
  </div>
  <p class="download-note">{download_note}</p>
</section>'''
    return full_page(f'Download · {title}', root, shell(content), label='Download', site_title=title)

def render_generated_pages_readme(title: str, generated_at: str) -> str:
    generated_line = generated_at or "not recorded"
    return f"""# {title}

Generated at: {generated_line}

This site publishes English documentation for a focused Lean 4 snapshot of
[Yamaguchi](https://n-yamaguchi-0729.github.io/homepage-en.html)'s formalized
library.
"""


def render_generated_pages_gitignore() -> str:
    return """__pycache__/
*.py[cod]
.DS_Store
Thumbs.db
"""


def canonical_public_html_url(public_site_url: str, relative_path: Path) -> str:
    base = public_site_url.rstrip('/') + '/'
    rel = relative_path.as_posix().lstrip('/')
    if rel == 'index.html':
        rel = ''
    elif rel.endswith('/index.html'):
        rel = rel[:-len('index.html')]
    return base + rel


def render_public_sitemap(public_site_root: Path, public_site_url: str) -> str:
    urls: list[str] = []
    for path in sorted(public_site_root.rglob('*.html'), key=lambda item: item.relative_to(public_site_root).as_posix()):
        rel = path.relative_to(public_site_root)
        if rel.name.lower().startswith('google'):
            continue
        urls.append(canonical_public_html_url(public_site_url, rel))
    entries = '\n'.join(f'  <url>\n    <loc>{escape(url)}</loc>\n  </url>' for url in urls)
    return f'''<?xml version="1.0" encoding="UTF-8"?>
<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">
{entries}
</urlset>
'''


def write_public_sitemap(public_site_root: Path, public_site_url: str) -> tuple[Path, bool, int]:
    public_site_root = public_site_root.resolve()
    require_directory(public_site_root, "public site root")
    sitemap_path = public_site_root / 'sitemap.xml'
    content = render_public_sitemap(public_site_root, public_site_url)
    changed = write_file(sitemap_path, content)
    return sitemap_path, changed, content.count('<url>')


def git_output(repo_root: Path, *args: str, timeout: int = 60) -> subprocess.CompletedProcess[str] | None:
    try:
        return subprocess.run(
            ["git", "-C", str(repo_root), *args],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None


def summarize_git_status(status_text: str, limit: int = 40) -> str:
    lines = [line for line in status_text.splitlines() if line.strip()]
    if not lines:
        return "  no working tree changes in generated paths"
    counts = Counter((line[:2].strip() or "changed") for line in lines)
    summary = ", ".join(f"{key}:{value}" for key, value in sorted(counts.items()))
    sample = "\n".join(lines[:limit])
    if len(lines) > limit:
        sample += f"\n  ... and {len(lines) - limit} more"
    return f"  {len(lines)} changed path(s) ({summary})\n{sample}"


def print_git_diff_summary(repo_root: Path, paths: list[str], reporter: BuildReporter | None = None) -> None:
    logger = reporter.progress if reporter else print
    status = git_output(repo_root, "status", "--short", "--", *paths)
    stat = git_output(repo_root, "diff", "--stat", "--stat-count=30", "--", *paths)
    shortstat = git_output(repo_root, "diff", "--shortstat", "--", *paths)
    staged = git_output(repo_root, "diff", "--cached", "--stat", "--stat-count=30", "--", *paths)
    staged_shortstat = git_output(repo_root, "diff", "--cached", "--shortstat", "--", *paths)
    logger("Git diff summary:")
    logger(summarize_git_status(status.stdout if status else ""))
    if shortstat and shortstat.stdout.strip():
        logger(shortstat.stdout.rstrip())
    if stat and stat.stdout.strip():
        logger(stat.stdout.rstrip())
    if staged_shortstat and staged_shortstat.stdout.strip():
        logger("Staged shortstat:")
        logger(staged_shortstat.stdout.rstrip())
    if staged and staged.stdout.strip():
        logger("Staged diff stat:")
        logger(staged.stdout.rstrip())


def commit_generated_pages(repo_root: Path, pages_root: Path, message: str, reporter: BuildReporter | None = None) -> bool:
    logger = reporter.progress if reporter else print
    rel_pages = pages_root.resolve().relative_to(repo_root.resolve()).as_posix()
    add = git_output(repo_root, "add", rel_pages, timeout=120)
    if add is None or add.returncode != 0:
        logger("Git commit skipped: failed to stage pages/.")
        if add and add.stderr.strip():
            logger(add.stderr.rstrip())
        return False
    staged = git_output(repo_root, "diff", "--cached", "--quiet", "--", rel_pages)
    if staged is not None and staged.returncode == 0:
        logger("Git commit skipped: no staged changes under pages/.")
        return False
    print_git_diff_summary(repo_root, [rel_pages], reporter)
    commit = git_output(repo_root, "commit", "-m", message, "--", rel_pages, timeout=120)
    if commit is None or commit.returncode != 0:
        logger("Git commit failed.")
        if commit and commit.stderr.strip():
            logger(commit.stderr.rstrip())
        return False
    logger(commit.stdout.rstrip())
    return True

def generate_site(
    lean_root: Path | None,
    out: Path,
    title: str,
    source_base_url: str = "",
    github_repo: str = "",
    commit: str = "",
    version: str = "",
    source_ref: str = "",
    assets_root: Path | None = None,
    generated_at: str = "",
    lean_distribution_package: str = DEFAULT_LEAN_PACKAGE_NAME,
    lean_distribution_zip: str = DEFAULT_LEAN_ZIP_NAME,
    lean_distribution_toolchain: str = "",
    lean_distribution_source_mirror: Path | None = None,
    mathlib_ref: str = "master",
    documentation_url: str = DEFAULT_DOCUMENTATION_URL,
    component_dirs: Iterable[Path] | None = None,
    module_components: dict[str, str] | None = None,
    component_display_names: dict[str, str] | None = None,
    library_metadata: list[dict[str, Any]] | None = None,
    source_root: Path | None = None,
    download_mode: str = DOWNLOAD_MODE_NONE,
    include_maintenance_files: bool = True,
    reporter: BuildReporter | None = None,
) -> WriteStats:
    reporter = reporter or BuildReporter(enabled=False)
    if lean_root is None and source_root is None:
        raise ValueError("lean_root or source_root is required")
    effective_source_root = Path(source_root or lean_root).resolve()
    component_dirs = (
        tuple(Path(path).resolve() for path in component_dirs)
        if component_dirs is not None
        else None
    )
    module_components = dict(module_components or {}) or None
    component_display_names = dict(component_display_names or {})
    library_metadata = list(library_metadata or [])
    if component_dirs is not None and module_components is not None:
        raise ValueError("component_dirs and module_components are mutually exclusive")
    if download_mode not in DOWNLOAD_MODES:
        raise ValueError(
            f"download_mode must be one of {sorted(DOWNLOAD_MODES)}: {download_mode!r}"
        )
    if (
        component_dirs is not None
        and download_mode == DOWNLOAD_MODE_DISTRIBUTION
    ):
        raise ValueError(
            "component directories require github-archive download mode; "
            "the legacy distribution ZIP assumes a flat Lean module tree"
        )
    out = out.resolve()
    assets_root = assets_root.resolve() if assets_root is not None else None
    stats = WriteStats()
    generated: set[str] = set()

    reporter.step("reading Lean documentation")
    modules, by_token = prepare_modules(
        lean_root,
        component_dirs=component_dirs,
        module_components=module_components,
        source_root=effective_source_root,
        fixed_updated_at=timestamp_epoch(generated_at),
    )
    module_names = {module.name for module in modules}
    resolved_module_components = {module.name: module.component for module in modules}
    decl_count = sum(len(module.decls) for module in modules)
    reporter.done(extra=f"{len(modules)} module(s), {decl_count} declaration(s)")

    reporter.step("preparing output directory")
    ensure_output_dir(out)
    previous = read_site_manifest(out)
    reporter.done(extra=f"{len(previous)} previously generated file(s)")

    def emit(rel_path: str, content: str) -> bool:
        return write_file(out / rel_path, content, out_root=out, generated=generated, stats=stats)

    package_name = lean_package_name(lean_distribution_package)
    zip_name = Path(lean_distribution_zip or DEFAULT_LEAN_ZIP_NAME).name or DEFAULT_LEAN_ZIP_NAME
    toolchain = lean_toolchain_for_distribution(
        effective_source_root, lean_distribution_toolchain
    )

    reporter.step("writing shared assets and index data")
    if include_maintenance_files:
        emit('README.md', render_generated_pages_readme(title, generated_at))
        emit('.gitignore', render_generated_pages_gitignore())
    emit('assets/site.css', read_static_asset('site.css', assets_root))
    emit('assets/site.js', read_static_asset('site.js', assets_root))
    if include_maintenance_files:
        emit(
            'tools/check_generated_site.py',
            (Path(__file__).resolve().parent / 'tools' / 'check_generated_site.py').read_text(encoding='utf-8'),
        )
        emit(
            'tools/public_paths.py',
            (Path(__file__).resolve().parent / 'public_paths.py').read_text(encoding='utf-8'),
        )
    if not source_base_url:
        source_base_url = github_source_base(github_repo, commit or source_ref or version)
    emit('assets/search-index.js', 'window.LEAN_DOCS_INDEX=' + json.dumps(build_search_index(modules, component_display_names), ensure_ascii=False, separators=(",", ":")) + ';\n')
    emit(
        'assets/tree-data.js',
        'window.LEAN_DOCS_TREE='
        + json.dumps(
            build_tree_data(modules, component_display_names),
            ensure_ascii=False,
            separators=(",", ":"),
        )
        + ';\n',
    )
    emit(
        'build-info.json',
        json.dumps(
            build_info_dict(
                title,
                version,
                commit,
                github_repo,
                effective_source_root,
                generated_at,
                source_ref,
                toolchain,
                library_metadata,
            ),
            ensure_ascii=False,
            indent=2,
        ) + '\n',
    )
    if include_maintenance_files:
        emit('.nojekyll', '')
    reporter.done(extra=f"{stats.written} written, {stats.unchanged} unchanged")

    archive_download_url = ""
    if download_mode == DOWNLOAD_MODE_DISTRIBUTION:
        reporter.step("building Lean distribution ZIP")
        with tempfile.TemporaryDirectory(prefix="lean-dist-") as tmp:
            project_root = Path(tmp) / package_name
            build_lean_distribution_zip(
                lean_root=effective_source_root,
                project_root=project_root,
                zip_path=out / "download" / zip_name,
                package_name=package_name,
                toolchain=toolchain,
                mathlib_ref=mathlib_ref,
                title=title,
                version=version,
                commit=commit,
                github_repo=github_repo,
                source_ref=source_ref,
                generated_at=generated_at,
                out_root=out,
                generated=generated,
                stats=stats,
                source_mirror_root=lean_distribution_source_mirror,
                reporter=reporter,
            )
        reporter.done()
    elif download_mode == DOWNLOAD_MODE_GITHUB_ARCHIVE:
        archive_download_url = pinned_github_archive_url(github_repo, commit)
        reporter.progress(
            "Using pinned GitHub source archive; no generated distribution ZIP "
            f"will be written: {archive_download_url}"
        )
    else:
        reporter.progress("Download page and generated ZIP are disabled")

    reporter.step("writing top-level pages")
    emit(
        'index.html',
        render_index(
            modules,
            title,
            github_repo,
            documentation_url,
            component_display_names,
        ),
    )
    emit('find/index.html', render_find_page(title, documentation_url))
    if download_mode != DOWNLOAD_MODE_NONE:
        emit(
            'download/index.html',
            render_download_page(
                title,
                version,
                commit,
                github_repo,
                source_ref,
                zip_name,
                package_name,
                archive_download_url,
            ),
        )
    reporter.done(extra=f"{stats.written} total written")

    reporter.step("writing module and source pages")
    link_map_cache: dict[str, dict[str, str]] = {}
    for module in modules:
        emit(
            module_html_path(module.name, module.component),
            render_module_page(
                module,
                modules,
                by_token,
                title,
                source_base_url,
                module_names,
                link_map_cache,
                documentation_url,
            ),
        )
        emit(
            source_html_path(
                module.rel_path,
                module.component,
                module.source_component_prefix,
            ),
            render_source_page(
                module,
                by_token,
                title,
                module_names,
                resolved_module_components,
                link_map_cache,
                documentation_url,
            ),
        )
        if len(generated) % 100 == 0:
            reporter.progress(f"Generated {len(generated)} file(s); {module.name}")
    reporter.done(extra=f"{len(modules) * 2} module/source page(s)")

    reporter.step("cleaning stale generated output")
    cleanup_stale_outputs(out, previous, generated, stats, reporter)
    if include_maintenance_files:
        write_site_manifest(out, generated, generated_at)
    else:
        manifest = out / SITE_MANIFEST_NAME
        if manifest.is_file() and not manifest.is_symlink():
            manifest.unlink()
            stats.deleted += 1
    reporter.done(extra=f"{stats.written} written, {stats.unchanged} unchanged, {stats.deleted} deleted")
    return stats


def read_site_config(repo_root: Path, data_root: Path) -> dict[str, Any]:
    for path in [data_root / "site_config.json", repo_root / "site_config.json"]:
        if path.exists():
            data = json.loads(path.read_text(encoding="utf-8"))
            return data if isinstance(data, dict) else {}
    return {}


def config_str(config: dict[str, Any], name: str, default: str = "") -> str:
    value = config.get(name, default)
    return str(value) if value is not None else default


def config_first_str(config: dict[str, Any], names: Iterable[str], default: str = "") -> str:
    for name in names:
        value = config.get(name)
        if value is not None and str(value).strip():
            return str(value)
    return default


def require_directory(path: Path, label: str) -> None:
    if not path.is_dir():
        raise FileNotFoundError(f"{label} was not found: {path}")


def require_git_repository(path: Path, label: str) -> None:
    require_directory(path, label)
    if not (path / ".git").exists():
        raise ValueError(f"{label} is not a Git repository: {path}")


def require_strict_descendant(parent: Path, child: Path, label: str) -> None:
    parent = parent.resolve()
    child = child.resolve()
    try:
        relative = child.relative_to(parent)
    except ValueError as exc:
        raise ValueError(f"{label} must stay inside {parent}: {child}") from exc
    if relative == Path("."):
        raise ValueError(f"{label} must not be the repository root: {child}")


def validate_publish_layout(
    *,
    repo_root: Path,
    pages_root: Path,
    published_pages_root: Path | None,
    lean_repository_mirror: Path,
    public_site_root: Path | None,
) -> None:
    """Reject unsafe sync targets before any generated files are written or removed."""
    workspace_root = repo_root.resolve().parent
    lean_repository_mirror = lean_repository_mirror.resolve()
    if lean_repository_mirror.parent != workspace_root:
        raise ValueError(
            f"Lean repository mirror must be a sibling of the generator directory: {lean_repository_mirror}"
        )
    require_git_repository(lean_repository_mirror, "Lean repository mirror")
    require_strict_descendant(lean_repository_mirror, pages_root, "Pages output")

    if published_pages_root is not None and public_site_root is None:
        raise ValueError("public_site_root is required when published_pages_root is configured")
    if public_site_root is None:
        return

    public_site_root = public_site_root.resolve()
    if public_site_root.parent != workspace_root:
        raise ValueError(
            f"Public site repository must be a sibling of the generator directory: {public_site_root}"
        )
    require_git_repository(public_site_root, "Public site repository")
    if public_site_root == lean_repository_mirror:
        raise ValueError("Lean and public site repositories must be different")
    if published_pages_root is not None:
        require_strict_descendant(
            public_site_root,
            published_pages_root,
            "Published pages output",
        )


def resolve_config_path(repo_root: Path, raw: str | Path) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = repo_root / path
    return path.resolve()


def require_repo_relative_path(repo_root: Path, path: Path, label: str) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError as exc:
        raise ValueError(f"{label} is outside this repository: {path}") from exc


def run_python_tool(
    repo_root: Path,
    *args: str,
    reporter: BuildReporter | None = None,
    label: str = "",
    required: bool = True,
) -> bool:
    if args:
        script = Path(args[0])
        script_path = script if script.is_absolute() else repo_root / script
        if script.suffix == ".py" and not script_path.exists():
            message = f"{'Missing required' if required else 'Skipping missing'} tool: {script_path}"
            if reporter:
                reporter.progress(message)
            else:
                print(message, flush=True)
            if required:
                raise FileNotFoundError(script_path)
            return False
    if reporter:
        reporter.step(label or " ".join(args))
    subprocess.run([sys.executable, *args], cwd=repo_root, check=True)
    if reporter:
        reporter.done()
    return True


def build_publish_pages(
    data_root: Path | None = None,
    *,
    show_git_diff: bool = True,
    commit_pages: bool = False,
    commit_message: str = "Build GitHub Pages",
    strict_checks: bool = False,
) -> None:
    reporter = BuildReporter()
    repo_root = Path(__file__).resolve().parent
    data_root = (data_root or repo_root / "data")
    if not data_root.is_absolute():
        data_root = repo_root / data_root
    data_root = data_root.resolve()

    lean_root = data_root / "lean4"
    assets_root = data_root / "assets"

    require_directory(data_root, "data")
    require_directory(lean_root, "data/lean4")
    require_directory(assets_root, "data/assets")
    assert_source_inventory(lean_root)

    config = read_site_config(repo_root, data_root)
    pages_root = resolve_config_path(repo_root, config_first_str(
        config,
        ("pages_output_root", "pages_root", "github_pages_root"),
        str(DEFAULT_PAGES_OUTPUT_ROOT),
    ))
    published_pages_root_raw = config_str(config, "published_pages_root")
    published_pages_root = (
        resolve_config_path(repo_root, published_pages_root_raw)
        if published_pages_root_raw
        else None
    )
    title = config_str(config, "title", "ProCGroups Documentation")
    github_repo = config_first_str(config, ("lean_github_repo", "lean_repository", "source_repository", "github_repo"))
    version = config_str(config, "version")
    commit = require_full_git_sha(config_str(config, "commit"), "data/site_config.json commit")
    source_ref = commit
    distribution_package = lean_package_name(config_str(config, "lean_package_name", DEFAULT_LEAN_PACKAGE_NAME))
    distribution_zip = Path(config_str(config, "lean_zip_name", DEFAULT_LEAN_ZIP_NAME)).name or DEFAULT_LEAN_ZIP_NAME
    distribution_toolchain = config_str(config, "lean_toolchain")
    lean_repository_mirror = resolve_config_path(repo_root, config_first_str(
        config,
        ("lean_repository_mirror", "lean_github_library_path"),
        str(DEFAULT_LEAN_REPOSITORY_MIRROR),
    ))
    distribution_source_mirror = lean_repository_mirror
    mathlib_ref = config_str(config, "mathlib_ref", "master")
    public_site_url = config_str(config, "public_site_url", DEFAULT_PUBLIC_SITE_URL)
    documentation_url = config_str(config, "documentation_url", DEFAULT_DOCUMENTATION_URL)
    public_site_root_raw = config_str(config, "public_site_root")
    public_site_root = resolve_config_path(repo_root, public_site_root_raw) if public_site_root_raw else None
    validate_publish_layout(
        repo_root=repo_root,
        pages_root=pages_root,
        published_pages_root=published_pages_root,
        lean_repository_mirror=lean_repository_mirror,
        public_site_root=public_site_root,
    )
    generated_at = git_commit_timestamp(lean_repository_mirror, commit)

    reporter.progress("Building publishable pages...")
    reporter.progress(f"data:  {data_root}")
    reporter.progress(f"pages: {pages_root}")
    reporter.progress(f"Lean repository mirror: {lean_repository_mirror}")
    reporter.progress(f"title: {title}")
    reporter.progress(f"generated_at: {generated_at}")
    cleanup_distribution_workdirs(repo_root, distribution_package, reporter=reporter)

    stats = generate_site(
        lean_root=lean_root,
        out=pages_root,
        title=title,
        github_repo=github_repo,
        commit=commit,
        version=version,
        source_ref=source_ref,
        assets_root=assets_root,
        generated_at=generated_at,
        lean_distribution_package=distribution_package,
        lean_distribution_zip=distribution_zip,
        lean_distribution_toolchain=distribution_toolchain,
        lean_distribution_source_mirror=distribution_source_mirror,
        mathlib_ref=mathlib_ref,
        documentation_url=documentation_url,
        reporter=reporter,
    )

    if published_pages_root is not None and published_pages_root.resolve() != pages_root.resolve():
        reporter.step("syncing generated pages to the public site repository")
        published_count = sync_directory_contents(pages_root, published_pages_root)
        reporter.done(extra=f"{published_count} file(s) synchronized to {published_pages_root}")

    generated_roots = [str(pages_root)]
    if published_pages_root is not None and published_pages_root.resolve() != pages_root.resolve():
        generated_roots.append(str(published_pages_root))
    run_python_tool(
        repo_root,
        "tools/check_generated_site.py",
        *generated_roots,
        reporter=reporter,
        label="validating generated documentation and pinned source links",
        required=strict_checks,
    )

    if public_site_root is not None:
        sitemap_path, sitemap_changed, sitemap_count = write_public_sitemap(public_site_root, public_site_url)
        sitemap_state = "updated" if sitemap_changed else "unchanged"
        reporter.progress(f"Public sitemap {sitemap_state}: {sitemap_path} ({sitemap_count} URL(s))")

    reporter.progress(
        f"Pages built successfully: {stats.generated} generated, {stats.written} written, "
        f"{stats.unchanged} unchanged, {stats.deleted} deleted"
    )
    if show_git_diff:
        print_git_diff_summary(repo_root, ["build_site.py", "data/site_config.json", ".gitignore"], reporter)
    if commit_pages:
        require_repo_relative_path(repo_root, pages_root, "pages output")
        commit_generated_pages(repo_root, pages_root, commit_message, reporter)
    reporter.progress(f"Open locally: {pages_root / 'index.html'}")
    publish_root = published_pages_root or pages_root
    reporter.progress(f"Publish by pushing the contents of {publish_root} to GitHub Pages.")


def windows_parent_process_names(limit: int = 4) -> list[str]:
    if os.name != "nt":
        return []
    try:
        import ctypes
        from ctypes import wintypes

        class PROCESSENTRY32W(ctypes.Structure):
            _fields_ = [
                ("dwSize", wintypes.DWORD),
                ("cntUsage", wintypes.DWORD),
                ("th32ProcessID", wintypes.DWORD),
                ("th32DefaultHeapID", ctypes.POINTER(wintypes.ULONG)),
                ("th32ModuleID", wintypes.DWORD),
                ("cntThreads", wintypes.DWORD),
                ("th32ParentProcessID", wintypes.DWORD),
                ("pcPriClassBase", wintypes.LONG),
                ("dwFlags", wintypes.DWORD),
                ("szExeFile", wintypes.WCHAR * 260),
            ]

        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        snapshot = kernel32.CreateToolhelp32Snapshot(0x00000002, 0)
        if snapshot == wintypes.HANDLE(-1).value:
            return []
        try:
            entry = PROCESSENTRY32W()
            entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
            processes: dict[int, tuple[int, str]] = {}
            ok = kernel32.Process32FirstW(snapshot, ctypes.byref(entry))
            while ok:
                processes[int(entry.th32ProcessID)] = (int(entry.th32ParentProcessID), entry.szExeFile)
                ok = kernel32.Process32NextW(snapshot, ctypes.byref(entry))
        finally:
            kernel32.CloseHandle(snapshot)

        names: list[str] = []
        current = os.getpid()
        for _ in range(limit):
            parent = processes.get(current)
            if not parent:
                break
            parent_pid, name = parent
            names.append(name.lower())
            current = parent_pid
        return names
    except Exception:
        return []


def should_pause_after_run(argv: list[str]) -> bool:
    if os.name != "nt" or len(argv) > 1:
        return False
    parents = windows_parent_process_names()
    return "explorer.exe" in parents or "openwith.exe" in parents


def pause_if_needed(enabled: bool) -> None:
    if enabled:
        try:
            input("\nPress Enter to close...")
        except EOFError:
            pass


def cleanup_python_caches(root: Path | None = None) -> None:
    root = root or Path(__file__).resolve().parent
    if not root.exists():
        return
    try:
        cache_dirs = sorted(root.rglob("__pycache__"), key=lambda path: len(path.parts), reverse=True)
        for cache_dir in cache_dirs:
            if ".git" in cache_dir.parts:
                continue
            shutil.rmtree(cache_dir, onerror=remove_readonly)
        for pattern in ("*.pyc", "*.pyo"):
            for cache_file in root.rglob(pattern):
                if ".git" in cache_file.parts:
                    continue
                try:
                    cache_file.unlink()
                except OSError:
                    remove_readonly(lambda path: Path(path).unlink(), str(cache_file), None)
    except OSError:
        pass


def remove_readonly(action: Any, path: str, _exc_info: Any) -> None:
    try:
        os.chmod(path, stat.S_IREAD | stat.S_IWRITE | stat.S_IEXEC)
        action(path)
    except OSError:
        pass


atexit.register(cleanup_python_caches, Path(__file__).resolve().parent)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate a static site for Lean source and prose statements.")
    parser.add_argument('--lean-root', type=Path, default=None, help='Directory containing the target .lean files.')
    parser.add_argument('--lean-github-repo', default='', help='Lean project GitHub URL or owner/repo. When set, the repository is cloned into a temporary directory.')
    parser.add_argument('--lean-ref', default='', help='Branch, tag, or commit to read with --lean-github-repo.')
    parser.add_argument('--out', type=Path, default=None, help='Output directory.')
    parser.add_argument(
        "--assets-root",
        type=Path,
        default=None,
        help=(
            "Directory containing site.css and site.js. "
            "Defaults to the bundled assets directory."
        ),
    )
    parser.add_argument('--title', default='ProCGroups Documentation', help='Site title.')
    parser.add_argument('--source-base-url', default='', help='Base URL for source links, usually generated from --github-repo and --commit.')
    parser.add_argument('--github-repo', default='', help='GitHub repository URL, for example https://github.com/user/repo')
    parser.add_argument('--commit', default='', help='Git commit SHA represented by the published site.')
    parser.add_argument('--version', default='', help='Displayed version name, for example v2026.04.30')
    parser.add_argument('--generated-at', default='', help='Deterministic public-page timestamp. Publish builds derive it from the pinned source commit.')
    parser.add_argument('--data-root', type=Path, default=Path('data'), help='Data directory used by the default build.')
    parser.add_argument('--publish-build', action='store_true', help='Generate the publishable site from data/ into pages/.')
    parser.add_argument('--no-git-diff', action='store_true', help='Do not print a git diff summary after building.')
    parser.add_argument('--commit-pages', action='store_true', help='Commit only pages/ changes after building.')
    parser.add_argument('--commit-message', default='Build GitHub Pages', help='Commit message used with --commit-pages.')
    parser.add_argument('--strict-checks', action='store_true', help='Fail if helper check tools are missing.')
    args = parser.parse_args()
    direct_build = args.lean_github_repo or args.lean_root is not None or args.out is not None
    if args.publish_build or not direct_build:
        build_publish_pages(
            args.data_root,
            show_git_diff=not args.no_git_diff,
            commit_pages=args.commit_pages,
            commit_message=args.commit_message,
            strict_checks=args.strict_checks,
        )
        return
    if args.out is None:
        parser.error('--out is required.')
    if args.lean_github_repo:
        with tempfile.TemporaryDirectory(prefix='lean-docs-') as tmp:
            lean_root = Path(tmp) / 'repo'
            clone_lean_repository(args.lean_github_repo, args.lean_ref, lean_root)
            github_repo = args.github_repo or normalize_github_repo(github_clone_url(args.lean_github_repo))
            commit = args.commit or git_head_commit(lean_root)
            generate_site(
                lean_root=lean_root,
                out=args.out,
                title=args.title,
                source_base_url=args.source_base_url,
                github_repo=github_repo,
                commit=commit,
                version=args.version,
                source_ref=args.lean_ref,
                assets_root=args.assets_root,
                generated_at=args.generated_at,
                reporter=BuildReporter(),
            )
        return
    if args.lean_root is None:
        parser.error('Either --lean-root or --lean-github-repo is required.')
    generate_site(
        lean_root=args.lean_root,
        out=args.out,
        title=args.title,
        source_base_url=args.source_base_url,
        github_repo=args.github_repo,
        commit=args.commit,
        version=args.version,
        source_ref=args.lean_ref,
        assets_root=args.assets_root,
        generated_at=args.generated_at,
        reporter=BuildReporter(),
    )


if __name__ == '__main__':
    pause = should_pause_after_run(sys.argv)
    try:
        main()
    except Exception as exc:
        print(f"\nBuild failed: {exc}", file=sys.stderr, flush=True)
        cleanup_python_caches()
        pause_if_needed(pause)
        raise SystemExit(1)
    cleanup_python_caches()
    pause_if_needed(pause)
