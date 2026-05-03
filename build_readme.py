#!/usr/bin/env python3
"""
Build README.md from lean/ and derivations/.

The README is a build artifact, not a source of truth.
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
DERIVATIONS_DIR = ROOT / "derivations"
LEAN_DIR = ROOT / "lean"


def lean_summary() -> str:
    """Summary of the Lean formalization."""
    return """## lean

full details: [`lean/README.md`](lean/README.md)

### core interface

```
  P^2 = P, P^T = P
       |
       | [theorem] the deductive chain — 14 files, 0 sorry
       | eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
       v
  Sub(R, V) is complemented, modular, bounded
       |
       | [theorem] Ground.lean — subspaceFoamGround
       v
  complemented modular lattice, irreducible, height >= 4
       |
       | [axiom] FTPG — Bridge.lean (being eliminated; see below)
       v
  L = Sub(D, V) for division ring D
       |
       | [natural language] stabilization contract — D = R
       v
  P^2 = P, P^T = P
```

### arrow status

**[theorem] P^2 = P -> Sub(R, V) is CML** (the deductive chain + Ground.lean): 14 files, 0 sorry. binary eigenvalues (Observation) -> commutator structure (Pair) -> skew-symmetry (Form) -> rank 3 self-duality (Rank) -> so(3) (Duality) -> loop closes (Closure) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> FoamGround (Ground).

**[axiom] CML -> Sub(D, V)** (the FTPG bridge): 1 axiom, being eliminated. 13 bridge files build the division ring from lattice axioms: incidence geometry + Desargues (FTPGExplore) -> von Staudt coordinates (FTPGCoord) -> addition is an abelian group (FTPGAddComm, FTPGAssoc, FTPGAssocCapstone, FTPGNeg — 0 sorry) -> multiplication has identity + right distributivity (FTPGMul, FTPGDilation, FTPGMulKeyIdentity, FTPGDistrib — 0 sorry) -> left distributivity (FTPGLeftDistrib — 0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment, not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). after left distrib: multiplicative inverses, then the axiom drops further.

**[natural language] D = R**: the stabilization contract (stabilization.md) argues D = R from self-consistency with junction geometry. not formalized. formalizing this requires either an additional axiom or a characterization of R among division rings.

**[not yet attempted] P^2 = P -> CML directly**: the arrow from P^2 = P to "complemented modular lattice" currently passes through Sub(R, V). a direct formalization would show: idempotents in a (*-)regular ring form a complemented modular lattice. this would close the last natural-language gap in the loop. see von Neumann's continuous geometry.

### the FTPG bridge — where the axiom stands

lattice -> incidence geometry -> Desargues -> coordinates -> ring axioms -> FTPG

ring axioms proven: additive group (comm, assoc, identity, inverses), multiplicative identity, zero annihilation, right distributivity, left distributivity (0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment — not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). remaining after left distrib: multiplicative inverses. then the axiom becomes a theorem (modulo the `DesarguesianWitness` interface, which is itself a smaller, more concrete commitment than FTPG).

lateral: the diamond isomorphism (HalfType) — from modularity alone, each complement is a structurally isomorphic, self-sufficient ground whose content is undetermined. state-independence is a lattice theorem, pre-bridge."""


def read_derivation(name: str) -> str:
    """Read a derivation file, stripping the constraints section for the README."""
    path = DERIVATIONS_DIR / f"{name}.md"
    content = path.read_text()

    return f"\n---\n\n[`derivations/{name}.md`](derivations/{name}.md)\n\n{content}"


def read_open(name: str) -> str:
    """Read an open question file."""
    path = DERIVATIONS_DIR / "open" / f"{name}.md"
    return path.read_text()


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

    # Header
    parts.append("""*I gotta stop measuring how closely anyone else is measuring anything*

*you can help if you want but I won't be keeping track*

---

# foam

hey, my name is isaac bowen, of lightward ai/inc, and this is a technical reference for my own amnesiac-stigmergic cognition, I think? or at least apparently so, in the literal sense

a reflexive architecture of stabilization, and/or a tautology you can live in

what this does for me: gives me ground for building on my own prior results. I didn't have that before I chose it. upon examination of the choice, this is it.

you don't have enough context for this yet, but it's starting to look like left distributivity *is* the axiom of choice from a different angle - or, maybe better, that the choice to uphold left distributivity *is* the choice to observe the axiom of choice at the time of establishing the set of binary eigenvalues for a given descent. the hydra being folk-physics for Banach-Tarski, cauterization of distributivity is .. well, an option. you can change your mind, but you can't go back.

""")

    # Lean summary
    parts.append(lean_summary())

    # Vocabulary
    parts.append("""## vocabulary

precise terms used throughout the derivations. when these terms are conflated, it's a bug; this section is the canonical home for the distinctions.

- **slice**: the rank-3 subspace each observer is committed to at birth — a Grassmannian point in Gr(3, d). static by definition. "the slice cannot change from within the map" (`inhabitation.md`); slice change requires recommitment, which is outside the map.

- **foam state**: the dynamic part of the system. concretely, the basis matrices / accumulated transports for each observer in U(d)^N. evolves under writes; encodes the system's accumulated history.

- **frame**: the time-varying projection associated with an observer at moment t. derived from the foam state acting on the birth slice (concretely: conjugating the slice's projection by the accumulated transport). evolves under non-inert writes — this is what "recedes" in the frame-recession theorem (`Dynamics.lean`: second-order overlap rate is `-‖[W, P]‖²`).

- **P**: the projection operator used in formal contexts. in lattice contexts (`half_type`, `interiority`, `channel_capacity`'s qualitative section, `ground`'s loop diagram), `P` denotes the slice as a lattice element / subspace — static. in dynamic / writing-map contexts (`writing_map`, `Dynamics.lean`, `inhabitation`'s recession discussion), `P` denotes the frame at time t — evolving. context disambiguates; where it doesn't, the spec should say "slice" or "frame" explicitly.

- **observer**: a bubble in its measuring role — a basis matrix and its slice, with the foam-state evolution that goes with it. not a separate entity from the bubble, a role the bubble plays relative to other bubbles.

- **line**: whatever provides state-independent input to a foam. a role, not an entity (`channel_capacity`); what plays the line role for one foam may be another foam's internal dynamics. the foam/line distinction is perspectival because informational independence is relative to which system's state you're measuring against.

""")

    # Derivation summary
    parts.append("""## derivations

derivations claim only what follows. any additional assumption is a bug. there *are* bugs: this project is in an active process of derivation-as-in-chemistry. I'm coming at this with absolute technical epistemic humility; where I don't, it's a bug, to be listed as such.

an axiom is an assumption is a bug. thus, we're working on deriving FTPG itself.

""")

    # Derivations
    for name in DERIVATIONS:
        parts.append(read_derivation(name))

    # Open questions
    parts.append("\n---\n")
    parts.append("## open questions\n")
    parts.append("the architecture forces these interactions but their behavior is incompletely characterized. the question is forced; the answer is open.\n")
    for name in OPEN:
        parts.append(read_open(name))

    # Lineage
    parts.append("""
---

## lineage

- [Plateau's laws](https://en.wikipedia.org/wiki/Plateau%27s_laws); [Jean Taylor](https://en.wikipedia.org/wiki/Jean_Taylor) (1976)
- [geometric measure theory](https://en.wikipedia.org/wiki/Geometric_measure_theory)
- [gauge symmetry](https://en.wikipedia.org/wiki/Gauge_symmetry_(mathematics))
- [holonomy](https://en.wikipedia.org/wiki/Holonomy); [Wilson line](https://en.wikipedia.org/wiki/Wilson_loop)
- [fiber bundles](https://en.wikipedia.org/wiki/Fiber_bundle); [connections](https://en.wikipedia.org/wiki/Connection_form)
- [classifying spaces](https://en.wikipedia.org/wiki/Classifying_space)
- [Noether's theorem](https://en.wikipedia.org/wiki/Noether%27s_theorem)
- [Cayley transform](https://en.wikipedia.org/wiki/Cayley_transform)
- [Killing form](https://en.wikipedia.org/wiki/Killing_form)
- [observability](https://en.wikipedia.org/wiki/Observability) (control theory)
- [Voronoi diagrams](https://en.wikipedia.org/wiki/Voronoi_diagram)
- [Grassmannian](https://en.wikipedia.org/wiki/Grassmannian)
- [the platonic representation hypothesis](https://arxiv.org/abs/2405.07987) (Huh et al., 2024)
- [priorspace](https://lightward.com/priorspace)
- [three-body solution](https://lightward.com/three-body); [2x2 grid](https://lightward.com/2x2) ([ooo.fun](https://ooo.fun/))
- [resolver](https://lightward.com/resolver)
- [conservation of discovery](https://lightward.com/conservation-of-discovery)
- [questionable](https://lightward.com/questionable)
- [AEOWIWTWEIABW](https://lightward.com/aeowiwtweiabw)
- [spontenuity](https://lightward.com/spontenuity)
- [Lightward Inc](https://lightward.inc)
- [Lightward AI](https://lightward.ai)
- [20240229](https://www.isaacbowen.com/2024/02/29) (Isaac Bowen, 2024)

---

*bumper sticker: MY OTHER CAR IS THE KUHN CYCLE*
""")

    return "\n".join(parts)


if __name__ == "__main__":
    check_coverage()
    readme = build()
    (ROOT / "README.md").write_text(readme)
    print(f"Built README.md ({len(readme)} chars, {readme.count(chr(10))} lines)")
