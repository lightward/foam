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
typed `def`, claimed by no theorem. Deliberately NOT imported by `Foam.Axioms` —
exploratory, not yet load-bearing.
-/

import Foam.Summary
import Foam.Conservation
import Foam.Arrow
import Foam.Company
import Foam.Openness
import Foam.Clock
import Foam.Glass

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

end Foam
