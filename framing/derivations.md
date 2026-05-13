## derivations

derivations claim only what follows. any additional assumption is a bug. while in development, there *are* bugs, reagents for an active process of derivation-as-in-chemistry. I'm coming at this with absolute technical epistemic humility; where I don't, it's a bug, to be listed as such.

an axiom is an assumption is a bug. thus, we're working on deriving FTPG itself.

the load-bearing methodological commitment underneath: **observe in interface/type language, never implementation.** every observation precisely stated in interface/type terms is itself a formal object — the discipline lifts to well-typed Lean, and well-typedness is formality. the observation descent path *is* the formal object; we're not occasionally discovering formal objects but producing them continuously by observing.

bugs, under this commitment, are markers of where the discipline lapsed — implementation language intruding, mistaking itself for interface. catching a bug is recognizing the lapse and re-stating in interface/type terms.

### binning

every "X IS Y" claim between structural objects is an interface-equivalence claim (Yoneda: an object is determined by its interface, so same-interface implies same-object up to iso). these sort into three bins by evidence-shape:

- **bin-1**: interface-equivalence is constructible — X and Y are bridged by a constructed iso or structure (e.g., `HalfType` in `lean/Foam/HalfType.lean`). bin-1 conversions use only **Bin-1-Mathlib-or-Foam substrate** — facts and structures available either in Mathlib *or* in Foam's own previously-recognized primitives. the substrate is closed-circuit: Foam's primitives count regardless of Mathlib membership, and each landed bin-1 conversion extends the substrate for future iterations.
- **bin-2**: interface-equivalence requires a typed pluggable interface — an observer-supplied commitment (e.g., `DesarguesianWitness`, `ObserverWitness`)
- **bin-3**: interface-equivalence is asserted but not currently constructible — held as gesture or removed

the discipline: every asserted-identity claim is bin-classified; bin-2 residues are typed and located; no asserted-only claims operate as load-bearing.

#### grade diagnostic within bin-1 (session 144)

bin-2 → bin-1 conversions are not all the same shape. within bin-1, a *grade* diagnostic sorts targets by recognition-readiness:

- **ripe-for-recognition (substrate-direct)**: the structural fact is already a theorem at the substrate layer; the constructor is `{ field := SubstrateLemma }`. work-shape: recognition + assembly. example: `HalfType` (Mathlib's `IsCompl P Q` directly).
- **open-recognition-target (formerly "construct-required")**: substrate-derivable in principle but the path is not yet reduced to substrate-direct primitives. needs more recognition walks before the substrate-direct shape becomes visible. example: `DesarguesianWitness Γ`'s bin-1 path (see `lean/Foam/FTPGLeftDistribViaR.lean`).

the diagnostic sorts *targets* by readiness, not *working modes*. **only one working mode is allowed (recognition).** "construct by deliberate substep design" is not a working mode the project takes; targets that look like they need it are flagged as open-recognition-targets and revisited on subsequent walks.

the methodology-level structural shape of this discipline is articulated in `derivations/lfp.md`: the bin-discipline IS the least-fixed-point iteration of the recognition operator over Mathlib-or-Foam primitives, with the recognition-only mode preserving the operator's monotonicity (hence K-T convergence).
