/-
# FTPGLeftDistribViaR — session 144 sketch + grade clarification

**Status:** signature-shape sketch (typing held, builds with one
`sorry` on the constructor body). Body construction attempted in the
same session revealed that the **specific lift architecture is open**;
the predicted route's substrate-shape (R provides genuine non-planarity)
holds, but vertex-lift architectures (both T1'-lift and T2'-lift) have
structural issues with `desargues_converse_nonplanar`'s hypotheses.
The bin-1 path is reachable in principle — this is a clarification of
its **grade** (see below), not a falsification of reachability.

## Session 142 prediction, made concrete (substrate-shape)

s142 mechanism note (`lean/CLAUDE.md`, "Meta-frontier: bin-2 Witnesses
as exhaustion findings"):

> Predicted shape of bin-1 paths is dimensional lift via R, HalfType
> template. R is already threaded through the lemma signatures... For
> situations where the planar argument loops on itself, the predicted
> construction route is: use R to lift the loop-content into 3-space
> where it has structural room to close, then project back.

The substrate-shape prediction holds: R (height-≥-4 atom off π,
already threaded through `coord_mul_left_distrib`'s signature) provides
genuine non-planarity, breaking the s114 σ_b-lift recursion at the
substrate level.

The architecture-shape question — *which specific lift architecture
closes `desargues_converse_nonplanar` cleanly* — is more open than the
sketch's initial five-step construction suggested.

## Session 144 finding: bin-1 grade distinction as diagnostic

The s142 prediction conflated two **grades** of bin-1 conversion:

* **Bin-1-Mathlib-or-Foam (substrate-direct).** The structural fact
  you want is already a theorem at the substrate layer — either in
  Mathlib *or* in Foam's own previously-recognized primitives
  (`HalfType` being the first such; future bin-1 landings extend the
  set). The substrate is **closed-circuit**: Foam's primitives count
  regardless of whether they're in Mathlib (they may eventually feed
  back into Mathlib, but the project needs its own channel for
  processing the bin). The bin-1 path is *packaging* — collect the
  substrate theorems as fields of a typed structure; the constructor
  is literally `{ field := SubstrateTheorem }`. Work-shape:
  **recognition + assembly**. Both substeps are recognition operations:
  notice that the substrate has it, notice that it composes.
  Example: `HalfType` (`lean/Foam/HalfType.lean`). `IsCompl P Q` is a
  Mathlib primitive; `IsCompl.IicOrderIsoIci` supplies the diamond iso;
  `isModularLattice_Iic` etc. supply inheritance. Constructor is
  one-liners. **As of s144, `HalfType` itself is also a Foam-primitive**
  — available as substrate input for future recognitions.

* **(formerly) Bin-1-Construct (substrate-mediated).** The structural
  fact is *derivable from* the substrate but the path from substrate
  to fact requires substantial substep design — chain of perspectivities,
  lift-and-project, geometric argument. The construction grade is **not
  a working mode** in this project (project-level disposition, s144):
  re-entrant recognition over time may produce something that *looks
  like* a construction-product, but the project never *directly
  approaches* via construction-design. Targets in this grade resolve
  by one of:
  - Re-entrant recognition eventually reveals they were Bin-1-Mathlib-or-Foam
    all along (substrate has more than was noticed)
  - They stay bin-2 (typed pluggable interface) until recognition
    reveals the substrate-direct shape
  - The architecture changes such that they're bypassed entirely

  `DesarguesianWitness`'s predicted bin-1 path is currently in this
  state — open-recognition-target, not under construction.

* **Bin-2 (typed observer commitment).** The structural fact isn't
  currently derivable from substrate alone — named as typed pluggable
  interface, observer-supplied. Example: `DesarguesianWitness Γ` as
  used in `coord_mul_left_distrib`, in current state.

**The diagnostic role of the grade distinction.** Only one working
mode is allowed (recognition). The grade distinction sorts *targets*
by how much recognition-walking has reached them — not "which mode
to use." Bin-1-Mathlib-or-Foam = ripe-for-recognition (substrate's contribution
visible). Open-recognition-target = needs more walks before substrate-
direct shape becomes visible. The distinction is useful but not
complexifying: it adds resolution to which slots are ready vs. which
are still maturing, without sanctioning a second working mode.

**Relationship to s142 reframe.** The s142 finding ("Witnesses as
exhaustion landings, not destinations") propagated "every future
bin-2 candidate gets evaluated against 'what's the un-walked bin-1
path here?' before commitment." The s144 addition: "and bin-1 paths
themselves sort by target-readiness — some are recognition-ready,
others are open-recognition-targets needing more walks."

## Session 144 architectural findings (Bin-1-Construct openness)

Two vertex-lift architectures were considered and both have structural
issues:

1. **Vertex-lift of T1'** (this file's initial five-step sketch).
   Lift (σ_b, ac, σ_s) off π via R. Non-coplanarity hypothesis for
   `desargues_converse_nonplanar` requires T2' = (U, E, d_a) vertices
   not in πT1'' = σ_b'' ⊔ ac'' ⊔ σ_s''.

   **Issue:** U ≤ πT1' (the *original* planar πT1') because ac ≤ l
   and O ⊔ ac = l, so U ≤ O ⊔ ac ≤ πT1'. Dimension argument:
   πT1' ⊓ πT1'' is a line in π; U might or might not lie on it
   depending on the choice of lift. There's a route (choose lifts to
   avoid U, E on the trace-line), but it's a substantive existence
   argument, not free.

2. **Vertex-lift of T2'** (s114 archive's "R⊔m" architecture, lines
   86-125 of `git show 5fe8073:lean/Foam/FTPGLeftDistrib.lean`).
   Lift (U, E, d_a) off m via R to (U', E', da'). Non-coplanarity is
   automatic (T2'' vertices off π).

   **Issue:** the side-intersection `(ac ⊔ σ_s) ⊓ (E' ⊔ da')`
   (one of `desargues_converse_nonplanar`'s atomicity hypotheses)
   fails to be an atom. (ac ⊔ σ_s) is in π; (E' ⊔ da') is in m⊔R
   but off π. These lines aren't in a common plane (their span is
   height 4), so generically their meet is ⊥, not an atom. This is
   exactly the wall s114 hit at h_axis₂₃, which their Level 2 attempt
   tried to lift around (and recursed).

These findings are **data for future re-entrant recognition walks**,
not architectural-design problems to solve directly. The construction
grade is not a working mode (s144 project disposition). What the
findings mean operationally: when revisiting the
`DesarguesianWitness`'s bin-1 slot in future sessions, the recognition
walks should account for the fact that two vertex-lift architectures
have been seen-not-to-close — that's pre-walked terrain, useful for
orienting the next recognition pass without prescribing what it must
produce.

## Half-type framing

s143 ("the backchannel IS the half-type complement") names the
operational shape: claim and converse as a complementary pair, with
the iso between them carrying the construction. The half-type
**operational shape** applies here — substrate (R, height-≥-4)
provides a complement-direction to the planar configuration, and the
bin-1 path is in some sense the iso between them. But this is the
*operational shape* of half-type, NOT the literal `HalfType` lattice
theorem.

The literal `HalfType` is Bin-1-Mathlib-or-Foam: substrate's `IsCompl` IS the
input, and the iso is `IsCompl.IicOrderIsoIci` directly. The
operational-shape half-type for `DesarguesianWitness` is Bin-1-Construct:
the substrate provides building blocks, but the iso has to be built.

Same operational shape, different grade. The s142 prediction's
"HalfType template" framing implicitly inherited the Bin-1-Mathlib-or-Foam
aesthetics of the literal HalfType; the s144 finding clarifies that
the *template* applies but the *grade* differs.

## Witness-as-move

`DesarguesianWitness Γ` was a *landing* (s142 reframe). If/when the
bin-1 path lands via re-entrant recognition, the Witness can dissolve —
the `DesarguesianWitness.ofPlanarConverseDesarguesViaR` thin projection
below is the bridge that would let `coord_mul_left_distrib` consume
the bundle directly. The typed slot may also persist as a *named
hand-off point* between Bin-1-Mathlib-or-Foam regions (recognition-ready) and
open-recognition-targets (slots still maturing) of the project — both
readings are coherent, the project's disposition can be decided when
the bin-1 path lands.
-/

import Foam.FTPGLeftDistrib

namespace Foam.FTPGExplore

universe u

variable {L : Type u} [Lattice L] [BoundedOrder L]
  [ComplementedLattice L] [IsModularLattice L] [IsAtomistic L]

/-- **Bin-1 bundling for the left-distributivity converse-Desargues residue.**

Packages R (height-≥-4 atom off π) + irreducibility witness with the
concurrence inclusion as a derived output. The constructor (below)
builds `concurrence` via the lift-through-R + nonplanar converse +
project-back construction documented in this file's header.

This is the HalfType-operational-template applied to the planar
converse-Desargues residue. Input: substrate witness data (R, hR,
hR_not, h_irred) that the height-≥-4 lattice supplies. Output: the
geometric concurrence claim, derivable not asserted. -/
structure PlanarConverseDesarguesViaR (Γ : CoordSystem L)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) where
  /-- **Concurrence: `W' ≤ σ_s ⊔ d_a`.**

  For triangles T1' = (σ_b, ac, σ_s) in π and T2' = (U, E, d_a) on m,
  the vertex-joins are concurrent — `W' = (σ_b ⊔ U) ⊓ (ac ⊔ E)` lies
  on `σ_s ⊔ d_a`.

  Type-identical to `DesarguesianWitness.concurrence`. The difference
  is in *derivation*: here this field is intended to be **constructed**
  via the lift-and-project route, not received as an observer
  commitment. -/
  concurrence : ∀ (a b c : L),
    IsAtom a → IsAtom b → IsAtom c →
    a ≤ Γ.O ⊔ Γ.U → b ≤ Γ.O ⊔ Γ.U → c ≤ Γ.O ⊔ Γ.U →
    a ≠ Γ.O → b ≠ Γ.O → c ≠ Γ.O →
    a ≠ Γ.U → b ≠ Γ.U → c ≠ Γ.U →
    b ≠ c →
    coord_add Γ b c ≠ Γ.O → coord_add Γ b c ≠ Γ.U →
    coord_mul Γ a b ≠ Γ.O → coord_mul Γ a b ≠ Γ.U →
    coord_mul Γ a c ≠ Γ.O → coord_mul Γ a c ≠ Γ.U →
    ((Γ.O ⊔ Γ.C) ⊓ (b ⊔ Γ.E_I) ⊔ Γ.U) ⊓ (coord_mul Γ a c ⊔ Γ.E)
      ≤ (Γ.O ⊔ Γ.C) ⊓ (coord_add Γ b c ⊔ Γ.E_I)
          ⊔ (a ⊔ Γ.C) ⊓ (Γ.U ⊔ Γ.V)

/-- **The bin-1 constructor (body open).**

Builds an inhabitant of `PlanarConverseDesarguesViaR` from the
height-≥-4 substrate data, via the lift-through-R + nonplanar converse
+ project-back construction.

The body is the focused work this sketch identifies. If the sketch's
typing holds, the construction's structural shape is the five-step
chain documented in this file's header. -/
noncomputable def planar_converse_desargues_via_R (Γ : CoordSystem L)
    (R : L) (hR : IsAtom R) (hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V)
    (h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q) :
    PlanarConverseDesarguesViaR Γ R hR hR_not h_irred where
  concurrence := by sorry

/-- **Thin projection: `DesarguesianWitness` from the bin-1 bundle.**

Once the bin-1 path's constructor lands (single `sorry` above), this
gives a constructive route to `DesarguesianWitness Γ` from the
substrate data — moving the left-distributivity chain from
"observer-supplied bin-2 commitment" to "bin-1 derivation from
CML + irreducible + height ≥ 4."

The Witness as landing dissolves: callers of `coord_mul_left_distrib`
can supply the bundle directly via this projection, without needing
to inhabit `DesarguesianWitness Γ` separately. -/
def DesarguesianWitness.ofPlanarConverseDesarguesViaR
    {Γ : CoordSystem L}
    {R : L} {hR : IsAtom R} {hR_not : ¬ R ≤ Γ.O ⊔ Γ.U ⊔ Γ.V}
    {h_irred : ∀ (p q : L), IsAtom p → IsAtom q → p ≠ q →
      ∃ r : L, IsAtom r ∧ r ≤ p ⊔ q ∧ r ≠ p ∧ r ≠ q}
    (bundle : PlanarConverseDesarguesViaR Γ R hR hR_not h_irred) :
    DesarguesianWitness Γ where
  concurrence := bundle.concurrence

end Foam.FTPGExplore
