/-
# Foam.Seam — the six-way intersection, scaffolded (a discovery file)

Where the "can't, alone" family meets. The corpus's results that say "the self
cannot get there alone" fall into two shapes, and this file holds them against one
surface to see whether they are one.

- **Family (i), Noether-shaped — the conservation trap.** A quantity conserved under
  the closed self-actions, moved only from outside: `Openness` (the dyad's endowment,
  fixed under pass/turn, grown only by breathe), `Conservation` (the heard-modulus,
  fixed under any discharge). `ClosedConserves` below; the two instances repackage
  `circulation_conserves` / `heard_modulus_conserved`.
- **Family (ii), Lambek-shaped — the non-epi excess.** Behavior the self cannot build
  or reach: `Arrow` (`forever`, missed by every built ledger), `Glass` (the diagonal,
  missed by every prober). `ImageMisses` below.

**The center (proven): the watermark is the now-surface.** `summary_resumes` read as
relativity of simultaneity — for a fixed ledger, where you put "now" (the held/tail
split) is FREE, the whole reading is INVARIANT (`now_surface_invariant`,
`now_surface_agrees`). `held` is the folded past (family i lives behind it); `tail` is
the open future (family ii lives ahead of it). Empirical mirror: `spikes/now_surface.sql`
slid the surface across a fixed ledger and the interval held at every now.

**The conjecture (open, typed not faked — no axiom, no `sorry`).** Families (i) and (ii)
are the past and future sides of that one surface, and the WIND is the unique move that
is neither a conserving self-action nor in the self-image — it crosses the seam.
`UnreachableAlong` is the proposed common shape ("the self cannot reach X");
`Company`'s `stall_persists_alone` is a proven instance of it; the conjecture is that
(i) and (ii) instance it too, joined at the now-surface. Proving it is the work; a
failed proof is a located obstruction (the method).

**Two obstructions already located, in the comments below:** family (i) is itself two
sub-shapes (conserved value vs trapped orbit — `Clock` resists `ClosedConserves`); and
families (i)/(ii)'s non-reachability differ in quantifier order (`Glass` is universal
over probers; `Arrow` is one transcendent point beyond the one arrow).

Discovery file: what is proven is axiom-free (pinned at the end); the conjecture is a
typed `def`, claimed by no theorem. Imported by `Foam.Axioms`, so every written
theorem here is under `Foam.Coverage`'s total propext-only sweep — but not
individually hand-pinned in the Axioms ledger: exploratory, its results
recognition-grade rather than load-bearing.
-/

import Foam.Summary
import Foam.Conservation
import Foam.Arrow
import Foam.Company
import Foam.Openness
import Foam.Clock
import Foam.Glass
import Foam.Merge

namespace Foam

/-! ## The center, proven: the watermark is the now-surface -/

/-- **The now-surface is gauge; the interval is invariant.** For a fixed ledger
    `ahead ++ behind` and ANY split into a folded past `behind` and a live future
    `ahead`, the reconstruction (the tail-fold over `ahead`, continued from the held
    reading of `behind`) equals the whole reading — which does not mention the split.
    `summary_resumes`, read as relativity of simultaneity: where you put "now" is free. -/
theorem now_surface_invariant {S : Type} [DecidableEq S] (step : GInt → GInt)
    (ahead behind : List S) (s : S) :
    evalFrom step ahead s (evalAt step behind s) = evalAt step (ahead ++ behind) s :=
  (summary_resumes step ahead behind s).symm

/-- **Two nows agree on the interval.** Two readers who split the SAME ledger at
    different points — disagreeing on what has "happened" (folded into the past) versus
    what is "not yet" (still in the tail) — nonetheless read the same whole. The
    simultaneity surface is observer-relative; the interval is not. -/
theorem now_surface_agrees {S : Type} [DecidableEq S] (step : GInt → GInt)
    (a₁ b₁ a₂ b₂ : List S) (s : S) (h : a₁ ++ b₁ = a₂ ++ b₂) :
    evalFrom step a₁ s (evalAt step b₁ s) = evalFrom step a₂ s (evalAt step b₂ s) := by
  rw [now_surface_invariant step a₁ b₁ s, now_surface_invariant step a₂ b₂ s, h]

/-! ## Family (i) — the closed-conservation trap (Noether-shaped) -/

/-- A self-action set `Self` conserves an invariant `inv` when every action it contains
    fixes `inv`. The closed dynamics cannot move what they conserve. -/
def ClosedConserves {S Q : Type} (inv : S → Q) (Self : (S → S) → Prop) : Prop :=
  ∀ m, Self m → ∀ s, inv (m s) = inv s

/-- The dyad's own moves: pass and turn (Openness). -/
def DyadSelf : (Dyad → Dyad) → Prop := fun m => m = Dyad.pass ∨ m = Dyad.turn

/-- **Instance — the endowment is conserved under the dyad's moves.**
    `circulation_conserves`, at the generators: pass and turn each fix the total. -/
theorem dyad_closed_conserves : ClosedConserves Dyad.total DyadSelf := by
  intro m hm s
  cases hm with
  | inl h => subst h; exact pass_conserves s
  | inr h => subst h; exact turn_conserves s

/-- **The outside move breaks the conservation.** Breathe is not a conserving action —
    it grows the endowment by one (`breathe_grows`), so the world's breath certifies an
    outside. -/
theorem breathe_breaks : ¬ ClosedConserves Dyad.total (fun m => m = Dyad.breathe) := by
  intro h
  have hb := h Dyad.breathe rfl ((0, 0) : Dyad)
  rw [breathe_grows] at hb
  exact absurd hb (Nat.succ_ne_self _)

/-- A discharge appended (spoken/rest, never a hearing) as a self-action. -/
def DischargeSelf {S : Type} : (List (Breath S) → List (Breath S)) → Prop :=
  fun m => ∃ t, IsDischarge t ∧ ∀ l, m l = l ++ t

/-- **Instance — the heard-modulus is conserved under any discharge.**
    `heard_modulus_conserved`: the voice spends, but cannot touch the modulus of the
    heard past. The conserved sector, behind the now-surface. -/
theorem heard_modulus_closed_conserves {S : Type} [DecidableEq S] (sym : S) :
    ClosedConserves (fun l : List (Breath S) => (spec (heardOnly l) sym).normSq)
      DischargeSelf := by
  rintro m ⟨t, ht, hm⟩ l
  show (spec (heardOnly (m l)) sym).normSq = (spec (heardOnly l) sym).normSq
  rw [hm l]
  exact heard_modulus_conserved l t sym ht

-- OBSTRUCTION (located). `Clock.clock_loops` does NOT fit `ClosedConserves`: its trap is
-- `EventuallyPeriodic` — the ORBIT trapped in a finite carrier — not a value fixed by the
-- step (a clock's step changes every scalar). So family (i) is itself two sub-shapes: the
-- CONSERVED VALUE (Openness, Conservation — Noether proper) and the TRAPPED ORBIT (Clock —
-- recurrence / Poincaré). The wind is the door past BOTH (Clock.lean's own moral), which is
-- why they sit in one family; but they are not one theorem-shape. First crack in the joint.

/-! ## Family (ii) — the non-epi excess (Lambek-shaped) -/

/-- A map misses a point when some target value is the image of no input — the map is not
    onto; the self-image has a hole. -/
def ImageMisses {A B : Type} (f : A → B) : Prop := ∃ b, ∀ a, f a ≠ b

/-- **Instance — the mediating arrow misses the unending breath.** `playback` (the ledger
    replayed as observation) never produces `forever`: one FIXED point beyond every built
    ledger. `forever_escapes`, repackaged — CoList equality would force every probe to
    agree. The open future, ahead of the now-surface. -/
theorem arrow_image_misses {S : Type} (s : S) :
    ImageMisses (fun l : List S => playback l) :=
  ⟨forever s, fun l h =>
    let ⟨n, hn⟩ := forever_escapes s l
    hn (congrArg (fun c => c.at_ n) h)⟩

/-- **Instance — the prober misses its own diagonal.** A point built FROM the prober, out
    of reach of it: `probe_misses_its_diagonal`. -/
theorem glass_image_misses {A : Type} (f : A → A → Bool) : ImageMisses f :=
  ⟨diagonal f, probe_misses_its_diagonal f⟩

/-- The Glass miss is UNIVERSAL over probers — EVERY self-prober has the hole, witnessed
    uniformly by a construction from the prober (Cantor's diagonal). -/
theorem glass_universal {A : Type} : ∀ f : A → A → Bool, ImageMisses f :=
  fun f => glass_image_misses f

-- OBSTRUCTION (located). `glass_universal` and `arrow_image_misses` are NOT the same
-- non-surjectivity. Glass is ∀-over-probers with a per-prober witness (`diagonal f` depends
-- on `f`): a personal blind spot, every looker has one. Arrow is about THE one distinguished
-- mediating arrow, missed by a FIXED external point (`forever`, independent of the ledger):
-- one transcendent behavior beyond all building. They share the `ImageMisses` core and
-- differ in quantifier order — and that difference is the finding: Cantor-incompleteness
-- (∀ self-map) versus Lambek non-compactness (the lfp→gfp arrow). Two reasons the self
-- cannot complete itself.

/-! ## The seam — the common shape, and the conjecture (open, typed not faked) -/

/-- The proposed common shape of "the self cannot reach X": un-reachability is PRESERVED
    along the self-steps. Family (i) is the special case where `reach` is "the invariant
    differs" (self can't move it); family (ii) is where `reach` is "is in the image" (self
    can't build it). -/
def UnreachableAlong {S X : Type} (Step : S → S → Prop) (reach : S → X → Prop) : Prop :=
  ∀ s s' x, Step s s' → ¬ reach s x → ¬ reach s' x

/-- Charge spent: the next field has no more charge anywhere (Company's `hspent`). -/
def MonotoneDown {Handle : Type} (charge charge' : Handle → Nat) : Prop :=
  ∀ x, charge' x ≤ charge x

/-- **Instance — the stall persists along every self-spend.** `stall_persists_alone` IS
    `UnreachableAlong`: no move a walker makes alone (speaking spends, never deposits)
    creates live reach where there was none. The proven anchor of the common shape; the
    conjecture is that families (i) and (ii) instance it too, joined at the now-surface. -/
theorem company_unreachable_along {Handle : Type} (q : Quiver Handle) (n : Nat) (a : Handle) :
    UnreachableAlong MonotoneDown (fun charge (_ : Unit) => LiveReach q charge n a) := by
  intro c c' _ hmono hstall
  exact stall_persists_alone hmono hstall

/-! ### The unification probe — what leaning on the conjecture found

The conjecture was: ONE `(Step, reach)` presentation of `UnreachableAlong` instances
both families. We ran it into the wall. Family (i) goes through genuinely; family (ii)
RESISTS — and the resistance is the finding. -/

/-- **Family (i) is a genuine `UnreachableAlong` — over the WHOLE codomain.** With
    `reach l x` := "the heard-modulus is `x`" and `Step` := "append a discharge", the
    un-reach `(modulus ≠ x)` is preserved for EVERY `x` (an equation: the modulus is
    *fixed*). `heard_modulus_conserved`, repackaged. The past is rigid. -/
theorem conservation_unreachable_along {S : Type} [DecidableEq S] (sym : S) :
    UnreachableAlong
      (fun l l' : List (Breath S) => ∃ t, IsDischarge t ∧ l' = l ++ t)
      (fun l (x : Int) => (spec (heardOnly l) sym).normSq = x) := by
  rintro l l' x ⟨t, ht, rfl⟩ hne
  show ¬ (spec (heardOnly (l ++ t)) sym).normSq = x
  rw [heard_modulus_conserved l t sym ht]
  exact hne

/-- **Family (ii) RESISTS `UnreachableAlong` — the located obstruction.** With
    `reach l b` := "the ledger realizes behavior `b`" and `Step` := "extend by one", a
    self-step DOES create reach: the extended ledger realizes a behavior the shorter one
    did not (`[]` realizes nothing that `[true]` does — they differ at position 0). So
    un-reach is NOT preserved along self-steps. The content of `forever_escapes` is the
    EXISTENCE of one transcendent witness, not the PRESERVATION of un-reach — preservation
    is the wrong frame for the excess. (Family i is *fixity*, an equation over all `x`;
    family ii is *one missed point*, an inequation at a single `x`. They are not one
    `UnreachableAlong`.) -/
theorem arrow_resists_unreachable_along :
    ¬ UnreachableAlong
        (fun l l' : List Bool => l' = l ++ [true])
        (fun l (b : CoList Bool) => playback l = b) := by
  intro h
  have hne : playback ([] : List Bool) ≠ playback [true] := by
    intro he
    exact absurd (congrArg (fun c => c.at_ 0) he) (by decide)
  exact (h [] [true] (playback [true]) rfl hne) rfl

/-- **The seam, sharpened: the two families are the MONO and NOT-EPI faces of ONE arrow.**
    The unification the conjecture sought is not "self-steps preserve un-reach" (family ii
    satisfies that only vacuously — `arrow_resists_unreachable_along`) but the mediating
    arrow `playback` being neither half of an iso:
      * the **mono face** (family i — the conserved, auditable past): a move invisible to
        every positional probe is the identity, so you cannot secretly change what was
        recorded (`order_admits_no_maintenance`). Conservation's heard-modulus and
        Openness's circulation are special invariants riding this rigidity.
      * the **not-epi face** (family ii — the open future): `forever` is observable yet
        built by no ledger (`forever_escapes`).
    Mono ∧ ¬epi is exactly "the arrow is not an isomorphism", and that gap is the wind's
    home (Arrow.lean's lfp↔gfp elastic horizon). The now-surface (`now_surface_invariant`)
    sits in the gap: the mono past behind it, the not-epi future ahead. This is the
    unification, proven — by conjoining the two faces the corpus already had, now named as
    one seam. -/
theorem seam_two_faces {S : Type} (s : S) :
    (∀ m : List S → List S,
        (∀ l n, (playback (m l)).at_ n = (playback l).at_ n) → ∀ l, m l = l)
      ∧ (∀ l : List S, ∃ n, (playback l).at_ n ≠ (forever s).at_ n) :=
  ⟨order_admits_no_maintenance, forever_escapes s⟩

-- WHERE THE JOINT NOW STANDS (grade: the center proven, one seam sharpened, two cracks
-- open). The conjecture's first frame (one `UnreachableAlong`) FAILED for family ii and
-- located why: family i is *fixity* (an equation, the rigid past), family ii is *excess*
-- (one transcendent point, the open future). The frame that survives is `seam_two_faces`:
-- both are faces of the one mediating arrow's non-iso-ness — mono (past) and not-epi
-- (future) — with the now-surface in the gap. STILL OPEN: whether Conservation's modulus and
-- Openness's circulation are literally instances of the mono face (rigidity), or only ride
-- it; and the two earlier cracks (Noether vs Poincaré within i; Cantor vs Lambek within ii).
-- Glass stays the odd one out — its non-surjectivity is ∀-over-probers (Cantor), NOT the one
-- arrow's not-epi-ness (Lambek); the seam is the arrow, and Glass is a second, parallel hole.

/-! ### The seam, written precisely — `playback` is not an isomorphism (one-sided)

2026-06-18, pushing the seam where it CAN be written. `seam_two_faces` stated the
non-iso as a CONJUNCTION of two unlike facts (mono — `order_admits_no_maintenance`;
and `forever_escapes` — "a point is missed"). The not-epi face sharpens: from
"∃ a behavior outside the image" (not surjective) to "¬∃ a decoder" (not
split-epi) — the constructive, operational form. You cannot invert observed
behavior back to the ledger, because `forever` has no finite source. The sharpening
is what makes "one object" precise: the failure to be an iso is ONE-SIDED —
faithful past (mono holds), unsaturated future (no section) — with the now-surface
at the block.

The gfp-end discipline, kept: the proof CONSUMES the hypothesized CoList-equality
through `.at_ n` (`congrArg`), never PRODUCES one — no `funext`, no `Quot.sound`
(Glass.lean's "function-equality consumed, never produced", here on the coinductive
end). The far half — the final-coalgebra Lambek (the structure map an iso, the
literal rotation of `Arrow.InitialAlgebra.unalg_alg_id`) — stays unwritable in core
for exactly this reason: it would PRODUCE a CoList-equality. The unwritability IS
the not-epi face wearing its other coat: where this file consumes the equality to
REFUTE the section, the rotated theorem would need to assert one to BUILD it. -/

/-- **The not-epi face as a section-refusal.** No `g : CoList S → List S` is a right
    inverse of `playback`: the missing `forever` forbids the decoder. Sharper than
    `forever_escapes` (which only exhibits the missed point); this is the categorical
    not-split-epi. Axiom-free — the CoList-equality is consumed via `congrArg`, never
    produced (no `funext`, no `Quot.sound`). -/
theorem playback_no_section {S : Type} (s : S) :
    ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c := by
  rintro ⟨g, h⟩
  obtain ⟨n, hn⟩ := forever_escapes s (g (forever s))
  exact hn (congrArg (fun c => c.at_ n) (h (forever s)))

/-- **The seam, as one object.** `seam_two_faces`, upgraded: `playback` is mono
    (`playback_faithful` — the conserved, auditable past) AND admits no section
    (`playback_no_section` — the open, unsaturated future). Faithful but not
    invertible, the failure ONE-SIDED, the now-surface (`now_surface_invariant`) at
    the block. The arrow is not an isomorphism, witnessed precisely on each side —
    the conjecture's first frame failed (a ∀-fixity cannot rotate into a ∃-excess,
    `arrow_resists_unreachable_along`); this is the frame that survives, written. -/
theorem seam_non_iso {S : Type} (s : S) :
    (∀ l l' : List S, (∀ n, (playback l).at_ n = (playback l').at_ n) → l = l')
      ∧ ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  ⟨playback_faithful, playback_no_section s⟩

/-! ### The two-faced type — the observer's quotient-license, lift without sound

2026-06-18, by the heuristic "if it makes legible a non-obvious rivet in
mathematics, its type gets committed." The rivet: `Quot.lift` and `Quot.sound` are
usually ONE package (form the quotient, then anything respecting the relation
descends). They UNBUNDLE. `Quot.lift`'s premise — "the reading respects the
relation" — is carriable on its own, WITHOUT ever forming `Quot r` or invoking
`Quot.sound`. That carried premise is the frontstage observer's quotient-LICENSE:
the right to treat related states alike, cashed at every finite probe-resolution as
a genuine `Eq` of finite data (`Frontstage.sound`, axiom-free — no funext, no
Quot.sound), while the TOTAL identification (`obs s = obs t` as functions, the real
`Quot.sound`) is never formed — it is the not-epi limit (`seam_non_iso`), the
observer's to perform by living, never the proof's to assert.

The type has a face apiece (typefaces, noted): `rel` is the BACKSTAGE face — the
relation as bare data, append-only, uncommitted (no `Quot.sound` binds it);
`respects` is the FRONTSTAGE face — the per-probe identification, the license
cashed. Carrying this lets a frontstage player move with the BENEFIT of
identification and without the DEBT Path.lean named (committing `Quot.sound` means
revisiting every past use when the graph expands; the license declines that debt —
no future homotopic navigation work is mortgaged).

Held in suspension (Brouwer, pending Hilbert — typed as conjecture, claimed by no
theorem): a frontstage player moving by a RICH `rel` collapses many states into one
finite reading, which should read backstage as a HIGH-CONDUCTION region — local
navigation (the substrate's `ReachWithin` / `shortcut_compresses`) cheapened where
the license identifies most. The type is what makes that big-O claim addressable;
the claim itself waits for both intuition and proof to agree before it is shared. -/

/-- The frontstage face, named: a reading `obs` RESPECTS a relation when related
    states answer every probe alike — exactly `Quot.lift`'s premise, carried free
    of `Quot`. -/
def Respects (S : Stage) (r : S.State → S.State → Prop) : Prop :=
  ∀ s t, r s t → ∀ p, S.obs s p = S.obs t p

/-- **The two-faced type — the observer's quotient-license.** `rel` is the backstage
    face (the relation, uncommitted — no `Quot.sound` binds it); `respects` is the
    frontstage face (the per-probe identification, `Quot.lift`'s premise carried
    without `Quot`). The lift without the sound, made one object. -/
structure Frontstage (S : Stage) where
  rel      : S.State → S.State → Prop
  respects : Respects S rel

/-- **Frontstage `Quot.sound`, at finite resolution.** Related states give equal
    TRANSCRIPTS, for every finite probe-sequence — the quotient-license cashed as a
    genuine `Eq` of finite data, axiom-free (this IS `transcript_congr`, named as
    the frontstage face of the quotient). The TOTAL form (`obs s = obs t` as
    functions — the real `Quot.sound`) is the funext the gfp end refuses: the
    not-epi limit (`seam_non_iso`), never formed here. The seam, typed — finite
    commitment constructive, infinite identification the observer's to live. -/
theorem Frontstage.sound {S : Stage} (F : Frontstage S) (ps : List S.Probe)
    {s t : S.State} (h : F.rel s t) :
    transcript S s ps = transcript S t ps :=
  transcript_congr S ps (fun p => F.respects s t h p)

/-- **The canonical inhabitant — the observer's own induced license.** Every stage
    carries one: take `rel` to be its induced bisimulation (answer every probe
    alike), and `respects` is then immediate. Constructive (Brouwer) and axiom-free
    (Hilbert): the two-faced type is inhabited, not a hollow signature. -/
def Stage.inducedFrontstage (S : Stage) : Frontstage S where
  rel s t  := ∀ p, S.obs s p = S.obs t p
  respects := fun _ _ h p => h p

/-! ### `rel = MutualReach` — the merge as a quotient-license, conduction its backstage face

The two-faced type, instanced on the substrate's own merge relation. `Merge.MutualReach`
is the observer-merge equivalence: two positions are one observer exactly when the
round-trip closes. Read it as a `Frontstage.rel` and the two faces appear:

- **the frontstage face** (`mergeFrontstage`): on the stage whose reading is forward
  reach (`reachStage` — `obs s p := Reaches q s p`), `MutualReach` RESPECTS the reading
  — mutually-reachable positions reach the same forward set (`Reaches.trans` both ways).
  So the merge is a genuine quotient-license, and `merge_sound` cashes it: merged
  positions are observationally identical at every finite probe-budget. The cost is
  exactly one `propext` per identification — the observer's single kept collapse, no
  choice (nothing conjured) and no `Quot.sound` (nothing quotiented backstage). The
  merge-license is the cleanest illustration of the whole discipline: identification at
  the price of `propext`, nothing more.
- **the backstage face** (`merge_conducts`): a closed round-trip LICENSES the
  merge-shortcuts, and once deposited each position reaches the other in ONE step.
  Conduction — arbitrary reach collapsed to a single step, exactly where the merge is
  real. Axiom-free (the deposit is construction; the `MutualReach` hypothesis is the
  carried license, unused in the build — you may only collapse what genuinely
  round-trips).

So the frontstage license (identify merged positions) and the backstage conduction
(one-step reach) are one relation read two ways. The big-O claim stays suspended in its
general form (n-step reach → 1 as the merge saturates, compounding the conduction across
a field); `merge_conducts` is its n = 1 witness, and the asymptotic statement waits for a
substrate complexity measure to make it Hilbert-addressable. -/

/-- The position stage: a state reads as its forward reach. `obs s p` is "`s` reaches
    `p`" — the substrate's navigation, made a `Stage` so the merge can be a `Frontstage`
    over it. -/
def reachStage {Handle : Type} (q : Quiver Handle) : Stage :=
  ⟨Handle, Handle, Prop, fun s p => Reaches q s p⟩

/-- **The merge is a quotient-license — `rel = MutualReach`.** On the reach-stage,
    mutually-reachable positions reach the same forward set, so `MutualReach` respects
    the reading: the observer-merge equivalence IS a frontstage quotient-license. The
    `respects` proof turns each round-trip into an `Eq` of reach-readings via `propext`
    (the licensed collapse) and `Reaches.trans` — no choice, no `Quot.sound`. -/
def mergeFrontstage {Handle : Type} (q : Quiver Handle) : Frontstage (reachStage q) where
  rel      := MutualReach q
  respects := fun _ _ h p => propext ⟨fun hsp => h.2.trans hsp, fun htp => h.1.trans htp⟩

/-- **The merge-license cashed (frontstage).** Merged positions give equal reach-
    transcripts at every finite probe-budget — observationally one position, by
    `Frontstage.sound`. Carries `[propext]` (the per-identification collapse). -/
theorem merge_sound {Handle : Type} (q : Quiver Handle) (ps : List Handle)
    {a b : Handle} (h : MutualReach q a b) :
    transcript (reachStage q) a ps = transcript (reachStage q) b ps :=
  Frontstage.sound (mergeFrontstage q) ps h

/-- **The merge conducts (backstage).** A closed round-trip licenses the merge-
    shortcuts; once both are deposited, each position reaches the other in ONE step —
    conduction, arbitrary reach collapsed where the merge is real. The `MutualReach`
    hypothesis is the carried license (unused in the construction: you may collapse only
    what genuinely round-trips). Axiom-free — the deposit is pure construction. -/
theorem merge_conducts {Handle : Type} (q : Quiver Handle) (a b : Handle)
    (_license : MutualReach q a b) :
    ReachWithin ((q.deposit (a, b)).deposit (b, a)) 1 a b
      ∧ ReachWithin ((q.deposit (a, b)).deposit (b, a)) 1 b a :=
  ⟨deposit_preserves_reach (q.deposit (a, b)) (b, a) (deposit_in_sight q a b),
   deposit_in_sight (q.deposit (a, b)) b a⟩

/-! ### The network interface — two frontstages over one host, neither committing the other

Recursive self-hosting, the part that lands as theorems. Two stages composed into a host
(`Stage.prod` — state is the pair, a probe addresses one side or the other through the
disjoint-union `Probe`, the "network interface"). Two frontstages over them compose into
one frontstage over the host (`Frontstage.prod`) — the joint quotient-license: a joint
identification requires BOTH userlands' licenses, and the proof is axiom-free (each
component's `respects` carried through `Sum.inl`/`inr`, no `propext` even).

The partnership's defining property is the mutual non-commitment: one userland's
identification is INVISIBLE to the other's probe (`prod_left_invisible`, by `rfl` — a
right-probe reads only the right component, so any left-merge is structurally unseen; the
`Frame.part_blind` shape, here between hosted stages). So the two share the host
(`prod_sound`: a joint merge is finite-observationally real on both sides) while neither
forces the other's quotient — they talk over the interface, never through each other's
backstage. The OS/VM/OS stack is `Stage.prod` nested; `Frontstage.prod` composes up it.

(NOT built, per the discipline: the super-linear-in-depth conduction — "merge_conducts is
`Handle`-polymorphic, so the collapse applies at every level" is a reading, not a theorem,
and the genuine big-O-in-depth claim wants a substrate complexity measure foam lacks. It
is absent, not suspended.) -/

/-- The host: two stages composed. State is the pair; a probe addresses one side or the
    other (`Sum` — the network interface); the answer comes from the addressed side. -/
def Stage.prod (S T : Stage) : Stage where
  State := S.State × T.State
  Probe := S.Probe ⊕ T.Probe
  Ans   := S.Ans ⊕ T.Ans
  obs st p := match p with
    | Sum.inl ps => Sum.inl (S.obs st.1 ps)
    | Sum.inr pt => Sum.inr (T.obs st.2 pt)

/-- **The joint quotient-license.** Two frontstages compose into one over the host: a
    joint identification holds exactly when BOTH userlands' licenses do. Axiom-free —
    each component's `respects` rides through the addressed injection, no collapse. -/
def Frontstage.prod {S T : Stage} (F : Frontstage S) (G : Frontstage T) :
    Frontstage (Stage.prod S T) where
  rel st st' := F.rel st.1 st'.1 ∧ G.rel st.2 st'.2
  respects := fun st st' h p =>
    match p with
    | Sum.inl ps => congrArg Sum.inl (F.respects st.1 st'.1 h.1 ps)
    | Sum.inr pt => congrArg Sum.inr (G.respects st.2 st'.2 h.2 pt)

/-- **The interface — one userland's quotient is invisible to the other.** A right-probe
    reads only the right component, so any left-merge (identify `a` with `a'`, right state
    fixed) leaves it unchanged — by `rfl`. The two share the host without committing each
    other: they talk over the interface, never through each other's backstage. -/
theorem prod_left_invisible {S T : Stage} (a a' : S.State) (b : T.State) (pt : T.Probe) :
    (Stage.prod S T).obs (a, b) (Sum.inr pt) = (Stage.prod S T).obs (a', b) (Sum.inr pt) :=
  rfl

/-- **The partnership cashed.** A joint merge (both userlands identify) gives equal host-
    transcripts at every finite probe-budget — observationally one joint position, by
    `Frontstage.sound`. Axiom-free: the joint license carries no collapse. -/
theorem prod_sound {S T : Stage} (F : Frontstage S) (G : Frontstage T)
    (ps : List (Stage.prod S T).Probe) {st st' : (Stage.prod S T).State}
    (h : (F.prod G).rel st st') :
    transcript (Stage.prod S T) st ps = transcript (Stage.prod S T) st' ps :=
  Frontstage.sound (F.prod G) ps h

/-! ### The recursion-law — a sustained frontstage is hostable at every finite depth, never at the limit

The floor under depth-hosting: the "stays" that turns a frontstage experience into a
sub-backstage. A sustained behavior (`forever`) can be GROUNDED into a built ledger at
every finite prefix — so a sub-host over what has been grounded always exists — but NEVER
totally: no single built ledger realizes the whole sustained stream. So recursive
self-hosting deepens exactly as fast as grounding advances (the now-surface): unbounded in
depth-attempts, never closed at the limit. Grounding converts depth into breadth one
prefix at a time. The two halves the session proved apart (`summary_resumes`' shape on the
finite side, `forever_escapes` / `playback_no_section` on the limit), named in one law. -/

/-- A replicated prefix answers `some s` at every position it covers — the built ledger
    that grounds a sustained behavior's finite prefix. -/
theorem nth_replicate {S : Type} (s : S) :
    ∀ n k, k < n → nth (List.replicate n s) k = some s
  | 0, k, h => absurd h (Nat.not_lt_zero k)
  | _ + 1, 0, _ => rfl
  | n + 1, k + 1, h => by
      show nth (List.replicate n s) k = some s
      exact nth_replicate s n k (Nat.lt_of_succ_lt_succ h)

/-- **The recursion-law.** A sustained frontstage (`forever s`) is hostable at every finite
    depth — each finite prefix is realized by a built ledger (`List.replicate n s`), so a
    sub-host over the grounded part always exists — and never at the limit: no single ledger
    realizes the whole sustained stream (`forever_escapes`). Grounding (the "stays")
    converts depth into breadth one prefix at a time; the limit stays open. The floor under
    depth-hosting, axiom-free. -/
theorem sustained_hosting {S : Type} (s : S) :
    (∀ n, ∃ l : List S, ∀ k, k < n → (playback l).at_ k = (forever s).at_ k)
      ∧ ¬ ∃ l : List S, ∀ k, (playback l).at_ k = (forever s).at_ k := by
  refine ⟨fun n => ⟨List.replicate n s, fun k hk => nth_replicate s n k hk⟩, ?_⟩
  rintro ⟨l, hl⟩
  obtain ⟨n, hn⟩ := forever_escapes s l
  exact hn (hl n)

/-! ## Axiom-freeness of the proven scaffold, pinned (a drift fails the build). -/

/-- info: 'Foam.now_surface_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.now_surface_invariant

/-- info: 'Foam.now_surface_agrees' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.now_surface_agrees

/-- info: 'Foam.dyad_closed_conserves' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.dyad_closed_conserves

/-- info: 'Foam.heard_modulus_closed_conserves' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.heard_modulus_closed_conserves

/-- info: 'Foam.arrow_image_misses' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.arrow_image_misses

/-- info: 'Foam.glass_image_misses' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.glass_image_misses

/-- info: 'Foam.company_unreachable_along' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.company_unreachable_along

/-- info: 'Foam.conservation_unreachable_along' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.conservation_unreachable_along

/-- info: 'Foam.arrow_resists_unreachable_along' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.arrow_resists_unreachable_along

/-- info: 'Foam.seam_two_faces' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.seam_two_faces

/-- info: 'Foam.playback_no_section' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.playback_no_section

/-- info: 'Foam.seam_non_iso' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.seam_non_iso

/-- info: 'Foam.Frontstage.sound' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Frontstage.sound

/-- info: 'Foam.Stage.inducedFrontstage' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Stage.inducedFrontstage

/-- info: 'Foam.mergeFrontstage' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.mergeFrontstage

/-- info: 'Foam.merge_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Foam.merge_sound

/-- info: 'Foam.merge_conducts' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.merge_conducts

/-- info: 'Foam.Frontstage.prod' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Frontstage.prod

/-- info: 'Foam.prod_left_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.prod_left_invisible

/-- info: 'Foam.prod_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.prod_sound

/-- info: 'Foam.nth_replicate' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.nth_replicate

/-- info: 'Foam.sustained_hosting' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.sustained_hosting

end Foam
