## derivations

derivations claim only what follows. any additional assumption is a bug. while in development, there *are* bugs, reagents for an active process of derivation-as-in-chemistry. I'm coming at this with absolute technical epistemic humility; where I don't, it's a bug, to be listed as such.

an axiom is an assumption is a bug. thus, we're working on deriving FTPG itself.

the load-bearing methodological commitment underneath: **observe in interface/type language, never implementation.** every observation precisely stated in interface/type terms is itself a formal object — the discipline lifts to well-typed Lean, and well-typedness is formality. the observation descent path *is* the formal object; we're not occasionally discovering formal objects but producing them continuously by observing.

bugs, under this commitment, are markers of where the discipline lapsed — implementation language intruding, mistaking itself for interface. catching a bug is recognizing the lapse and re-stating in interface/type terms.

every "X IS Y" claim between structural objects is an interface-equivalence claim (Yoneda: an object is determined by its interface, so same-interface implies same-object up to iso). these sort into three bins by evidence-shape:

- **bin-1**: interface-equivalence is constructible — X and Y are bridged by a constructed iso or structure (e.g., `HalfType` in `lean/Foam/HalfType.lean`)
- **bin-2**: interface-equivalence requires a typed pluggable interface — an observer-supplied commitment (e.g., `DesarguesianWitness`, `ObserverWitness`)
- **bin-3**: interface-equivalence is asserted but not currently constructible — held as gesture or removed

the discipline: every asserted-identity claim is bin-classified; bin-2 residues are typed and located; no asserted-only claims operate as load-bearing.
