"""Canonical public URL paths for generated Lean documentation."""

from __future__ import annotations

from pathlib import PurePosixPath


def _public_parts(
    parts: tuple[str, ...],
    component: str,
    strip_component_prefix: bool | None,
    *,
    source_label: str,
) -> tuple[tuple[str, ...], bool]:
    """Strip one matching library prefix and report whether it was removed."""
    should_strip = (
        bool(component and parts and parts[0] == component)
        if strip_component_prefix is None
        else strip_component_prefix
    )
    if should_strip:
        if not component or not parts or parts[0] != component:
            raise ValueError(
                f"{source_label} is not inside component {component!r}"
            )
        parts = parts[1:]
    return parts, should_strip


def _html_parts(
    parts: tuple[str, ...],
    component: str,
    strip_component_prefix: bool | None,
    *,
    source_label: str,
) -> tuple[str, ...]:
    """Choose a structurally collision-free route for a library-owned module."""
    public_parts, stripped = _public_parts(
        parts,
        component,
        strip_component_prefix,
        source_label=source_label,
    )
    if stripped:
        return public_parts or ("root-module",)
    if component:
        return ("module-roots", *public_parts)
    return public_parts


def module_html_path(
    module: str,
    component: str = "",
    strip_component_prefix: bool | None = None,
) -> str:
    """Return the canonical HTML path for a Lean module."""
    parts = tuple(module.split("."))
    public_parts = _html_parts(
        parts,
        component,
        strip_component_prefix,
        source_label=f"module {module!r}",
    )
    prefix = f"library/{component}/" if component else "library/"
    return prefix + PurePosixPath(*public_parts).with_suffix(".html").as_posix()


def source_html_path(
    rel_lean_path: str,
    component: str = "",
    strip_component_prefix: bool | None = None,
) -> str:
    """Return the canonical HTML path for a rendered Lean source file."""
    source_path = PurePosixPath(rel_lean_path)
    source_parts = source_path.with_suffix("").parts
    public_strip = strip_component_prefix
    if strip_component_prefix:
        if not component or not source_parts or source_parts[0] != component:
            raise ValueError(
                f"source path {rel_lean_path!r} is not inside component "
                f"{component!r}"
            )
        source_parts = source_parts[1:]
        public_strip = None
    public_parts = _html_parts(
        source_parts,
        component,
        public_strip,
        source_label=f"source path {rel_lean_path!r}",
    )
    prefix = f"library/{component}/src/" if component else "library/src/"
    return prefix + PurePosixPath(*public_parts).with_suffix(".html").as_posix()
