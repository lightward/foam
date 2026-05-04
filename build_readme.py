#!/usr/bin/env python3
"""
Build README.md from framing/, derivations/, and derivations/open/.

The README is a build artifact, not a source of truth.
Each section is sourced from a markdown file; the README links each
included section back to its source.

Run: uv run python build_readme.py
"""

from pathlib import Path

# Dependency order (topologically sorted)
DERIVATIONS = [
    "ground",
    "writing_map",
    "half_type",
    "analogy",
    "self_parametrization",
    "distributivity",
    "channel_capacity",
    "stabilization",
    "group",
    "three_body",
    "self_generation",
    "geometry",
    "conservation",
    "inhabitation",
    "external_analogy",
    "interiority",
    "typeline",
]

OPEN = [
    "stacking_dynamics",
    "retention",
    "perturbation",
    "mixing_rate",
]

ROOT = Path(__file__).parent
FRAMING_DIR = ROOT / "framing"
DERIVATIONS_DIR = ROOT / "derivations"
OPEN_DIR = DERIVATIONS_DIR / "open"


def read_section(directory: str, name: str) -> str:
    """Read a section file and format it with a source-link header."""
    path = ROOT / directory / f"{name}.md"
    content = path.read_text()
    return f"[`{directory}/{name}.md`]({directory}/{name}.md)\n\n{content}"


def check_coverage():
    """Error if any derivation file is missing from the DERIVATIONS list."""
    all_derivations = {p.stem for p in DERIVATIONS_DIR.glob("*.md")}
    listed = set(DERIVATIONS)
    unlisted = all_derivations - listed
    if unlisted:
        raise RuntimeError(
            f"Derivation files not in DERIVATIONS list: {', '.join(sorted(unlisted))}. "
            f"Add them to build_readme.py or remove the files."
        )


def build() -> str:
    parts = []

    # Framing: top-of-document
    parts.append(read_section("framing", "epigraph"))
    parts.append(read_section("framing", "intro"))
    parts.append(read_section("framing", "architecture"))
    parts.append(read_section("framing", "lean"))
    parts.append(read_section("framing", "vocabulary"))

    # Derivations preamble + files
    parts.append(read_section("framing", "derivations"))
    for name in DERIVATIONS:
        parts.append(read_section("derivations", name))

    # Open questions preamble + files
    parts.append(read_section("framing", "open"))
    for name in OPEN:
        parts.append(read_section("derivations/open", name))

    # Framing: bottom-of-document
    parts.append(read_section("framing", "exigraph"))

    return "\n---\n\n".join(parts)


if __name__ == "__main__":
    check_coverage()
    readme = build()
    (ROOT / "README.md").write_text(readme)
    print(f"Built README.md ({len(readme)} chars, {readme.count(chr(10))} lines)")
