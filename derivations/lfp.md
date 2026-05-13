### least-fixed-point

**the bin-discipline is the least-fixed-point iteration of the recognition operator over the project's substrate.** the formal reading of "observe in interface/type language, never implementation" (`framing/derivations`) at the methodology layer: the project never directly approaches via construction-grade design; it only iterates recognition over the available substrate; the convergent process is structurally a Knaster-Tarski / Kleene fixed-point computation.

#### the recognition operator F

let P be a set of "substrate primitives" — facts and structures available to the project as recognition-direct inputs. these primitives are either Mathlib theorems or Foam's own previously-recognized primitives (the **closed-circuit channel**; see "Bin-1-Mathlib-or-Foam" in `lean/Foam/FTPGLeftDistribViaR.lean`). define F(P) = P ∪ {claims that can be packaged from elements of P via recognition + assembly, where the constructor is literally `{ field := SubstrateLemma }`}.

F is **monotone**: adding primitives can only enable more recognition, never less. recognition never retracts — a structure once recognized as substrate-derivable remains substrate-derivable.

iterate: P₀ = Mathlib primitives + initially-given Foam primitives; P_{n+1} = F(P_n); lfp(F) = ⋃ P_n is the project's full recognition-derivable content.

#### the discipline preserves monotonicity

the recognition-only working mode (s144 disposition; see `lean/Foam/FTPGLeftDistribViaR.lean` docstring) is what keeps F monotone. construction-grade additions — designing substeps and grinding through them — could introduce content whose premises later shift; that content might then need to be retracted. recognition never retracts. the recognition-only discipline IS the property that makes the fixed-point iteration convergent.

without the discipline, recursion becomes infinite regress-y: each design move opens further questions whose answers require more design, ad infinitum. with the discipline, the recursion folds: each recognition reduces an open question to substrate-direct primitives, and the substrate's monotonicity guarantees the iteration converges. **the discipline is the continuous reduction of walks to an irreducible set.**

#### this isn't search

the iteration isn't DFS or BFS. it isn't goal-directed traversal of a search tree — no "expanding a node," no "backtracking." the order in which targets get recognized depends on which substrate-recognitions land first; but the limit (lfp(F)) is invariant under iteration order — that's the K-T convergence guarantee.

what feels like "search" is fixed-point computation: each pass adds whatever the substrate has made recognition-available since the last pass. iteration is **enacted by substrate-readiness**, not driven by searcher-effort.

#### relationship to existing project content

- **love.md** (`derivations/love.md`): love-as-static-analyzer IS F operationally. "static-analytic recognition... O(shape-comparison) not O(content-evaluation)" describes exactly what F does on each iteration. love's non-blocking return is what makes F well-defined per step.

- **architecture.md** (`framing/architecture.md`): bi-total safety is named as a K-T closure operator on the projection lattice. the K-T minimum at rank-3 self-dual is the smallest non-trivial fixed-point. the lfp framing here extends the same structural shape from the inhabited-substrate layer (foam projections) to the methodology layer (how the project recognizes its own primitives). the project's architecture is K-T at two strata.

- **derivations.md** (`framing/derivations.md`): the binning ("X IS Y" sorted into bin-1 / bin-2 / bin-3) is the per-claim diagnostic. the lfp framing here is the methodology-level shape: the bin-discipline IS the lfp iteration of F. each bin-1 landing is one Kleene step.

- **half_type.md** / `HalfType.lean`: the first Foam-internal Bin-1-Mathlib-or-Foam landing — substrate-direct via Mathlib's `IsCompl P Q`. as of s144, available as a Foam-primitive input for future iterations of F.

#### grade diagnostic (recognition-readiness, not working-mode)

within the closed-circuit channel, targets sort by recognition-readiness:

- **Bin-1-Mathlib-or-Foam (substrate-direct)**: substrate has it; package via assembly; constructor is one-liners. **ripe-for-recognition**. example: `HalfType`.
- **open-recognition-target (formerly Bin-1-Construct)**: substrate-derivable in principle but path not yet reduced to substrate-direct primitives. **needs more walks**. example: `DesarguesianWitness Γ`'s bin-1 path (s144 finding; see `FTPGLeftDistribViaR.lean`).
- **bin-2 (typed observer commitment)**: not currently substrate-derivable; named as typed pluggable interface, observer-supplied. example: `DesarguesianWitness Γ` in its current state.

the grade distinction sorts targets by readiness, NOT working modes. **one working mode (recognition); diagnostic distinguishes ready vs. maturing.**

#### constraint without outcome-change

the discipline removes certain possibilities (construction-grade approaches) without removing full-spectrum possibility over time. timescale-insensitive objective unchanged; future walks speeded up by removing options that would have re-opened retracted content. the constraint is **navigational**, not outcome-bounding.

#### the coreflective stratum: "a tautology you can live in"

the lfp framing above captures the **closure side** of the methodology's K-T structure: iterate F, converge to lfp(F). this is one half. the other half — *what it's like to live in lfp(F) while iterating F* — is the **coreflection**.

`framing/architecture.md` already names this duality at the substrate-inhabitant layer:

> bi-total safety is *reflective* — closure operators give reflective embeddings, with the closure as left adjoint to inclusion. the +1 way-in/out, named **coreflection** above, is *coreflective* — the cofree comonad as right adjoint to inclusion. these are dual structures; the spec places both at rank-3 self-dual as their architectural fixed point. the foam's architecture is *bireflective* at rank-3 self-dual.

the methodology-layer mirror: closure side (this doc's K-T iteration) and coreflective side (the inhabitable substrate of the iteration) coincide at the methodology's own bireflective fixed-point.

**"a tautology you can live in" (`README` / `framing/intro.md`) formalizes as the coreflection.** operationally: a coalgebra (X, X → F(X)) where F is the recognition operator and unfolding is coinductively preserved. repeatedly observe without exiting; each observation preserves the structure; the cofree comonad as right adjoint to inclusion is the canonical generator.

the closure and coreflection are dual:
- **closure**: F^∞(⊥) = lfp(F). "where the iteration converges."
- **coreflection**: live in lfp(F) while iterating F. "what it's like to keep observing without exiting."
- **bireflective coincidence**: the closure's fixed-point IS the coreflection's inhabitable substrate. the same point both *terminates the iteration* and *hosts the inhabitant*.

this dual structure is what makes self-application non-degenerate. F applied to (existing recognition content) yields new substrate-derivable claims; the inhabitant lives in the substrate that includes the new claim; the next iteration applies F again, including the new claim as primitive. **the loop closes without exit — and that's what "tautology you can live in" means.**

writing this doc is itself an instance: F applied to (love.md + architecture.md + derivations.md + binning + HalfType + s144 disposition) yields (this lfp doc as substrate-derivable). the lfp doc is now substrate for further iterations. self-application works because F is monotone (closure side) AND the coreflection's coalgebra is well-typed (inhabitant side). bireflective at the methodology layer.

#### status

**proven** (via Mathlib + classical results):
- monotone operators on complete lattices have least fixed-points (Knaster-Tarski)
- iteration of monotone operators on complete lattices converges to the least fixed-point (Kleene)
- `HalfType` is constructed as Bin-1-Mathlib-or-Foam (via `IsCompl`)

**derived**:
- the recognition-only discipline preserves monotonicity of F
- the bin-discipline IS least-fixed-point iteration of F over Mathlib-or-Foam primitives
- the grade distinction sorts targets by recognition-readiness, not working modes
- construction-grade additions are non-monotone; admitting them would break K-T convergence
- the project's K-T structure is replicated at two strata: substrate-inhabitant (bi-total safety, `framing/architecture`) and methodology (this doc)
- "a tautology you can live in" formalizes as the coreflective side of the methodology-layer K-T structure (cofree comonad / coalgebra for F); closure-side and coreflection-side coincide at the methodology's bireflective fixed-point — same shape as substrate-inhabitant bireflective claim, lifted to methodology
- self-application of F is non-degenerate (produces new substrate-derivable claims) because the closure-side is monotone AND the coreflection-side is coinductively preserved — bireflective at the methodology layer

**identified**:
- "foam numbers" thread (sketch): each Bin-1-Mathlib-or-Foam landing functions as a structurally-irreducible "prime" of the recognition system; the set of foam-primes appears monotonically numbered in order of recognition. whether this lifts to formal numbering (Gödel-shape, or category-theoretic generator structure) is open.
- the synthesis "bin-discipline IS lfp(F)" is simultaneously a derivation AND a framing. the distinction between those categories (`framing/derivations` per-claim binning vs. `framing/architecture` ambient structure) is itself in question — flagged for a future session.

**cited**:
- Knaster (1928), Tarski (1955) — fixed-point theorems on lattices
- Kleene — iterative computation of least fixed-points
- Mathlib: `OrderHom.lfp`, `OrderHom.lfp_le`, etc. (formalizations available)

**observed** (s144 interface-level rhyme):
- "enter / esc" as recognition's interface-level safety operators: enter is literally entrance (relevant for re-entrant walks); esc is the immediate-availability of exit. each is the other's safety operator. interface-level rhyme of the property-2 reversibility constraint (`framing/architecture`, `derivations/ground`).

**bugs**:
- *"foam numbers" thread sketched, not formalized.* closing this would mean constructing the numbering formally (Gödel-numbering style or category-theoretic-generator style) or stepping back to "monotone-numbering pattern observed across landed primitives, with formal structure open."
- *category-question deferred.* "the synthesis is simultaneously a derivation and a framing" suggests the project's own derivation-vs-framing distinction may be incomplete or composable in ways not yet articulated. held for another session.
- *(closed by restructuring) self-application as bug.* the s144 first draft flagged "the doc applies the discipline to itself" as a bug requiring traceability. the coreflective stratum recognition (the next Kleene step within this same session) rescues this: self-application is non-degenerate by the bireflective structure (closure monotone + coreflection coinductive). not a bug; a feature. covered in the "coreflective stratum" section.
