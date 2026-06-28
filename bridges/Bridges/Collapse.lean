import Bridges.Encounter
import Foam.Platonism
import Foam.Seat.Descend

namespace Foam.Bridges

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
variable {State : Type}

structure HalfShape (X A : Type) where
  e      : X → X
  obs    : X → A
  idem   : ∀ x, e (e x) = e x
  unseen : ∀ x, obs (e x) = obs x

def HalfShape.Free {X A : Type} (H : HalfShape X A) : Prop := ∃ x, H.e x ≠ x

theorem HalfShape.image_eq_fixed {X A : Type} (H : HalfShape X A) (x : X) :
    (∃ y, H.e y = x) ↔ H.e x = x := by
  constructor
  · rintro ⟨y, rfl⟩; exact H.idem y
  · intro hx; exact ⟨x, hx⟩

theorem HalfShape.rep_unseen {X A : Type} (H : HalfShape X A) (x : X) :
    H.e (H.e x) = H.e x ∧ H.obs (H.e x) = H.obs x :=
  ⟨H.idem x, H.unseen x⟩

def projHalfShape (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) : HalfShape V V where
  e := P
  obs := P
  idem := fun x => by
    have := LinearMap.ext_iff.mp h_idem x
    simpa [LinearMap.comp_apply] using this
  unseen := fun x => by
    have := LinearMap.ext_iff.mp h_idem x
    simpa [LinearMap.comp_apply] using this

theorem projHalfShape_collapses_e_obs (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) :
    (projHalfShape P h_idem).e = (projHalfShape P h_idem).obs := rfl

theorem projHalfShape_free (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P)
    (hf : ∃ v, P v ≠ v) : (projHalfShape P h_idem).Free := hf

def dressHalfShape (b : Foam.Beholder State) :
    HalfShape (State × Int) (b.Probe → b.Ans) where
  e := fun s => (s.1, 0)
  obs := fun s p => b.obs s.1 p
  idem := fun _ => rfl
  unseen := fun _ => rfl

theorem dressHalfShape_free (b : Foam.Beholder State) (s₀ : State) :
    (dressHalfShape b).Free := by
  refine ⟨(s₀, 1), fun h => ?_⟩
  have h2 : (0 : Int) = 1 := congrArg Prod.snd h
  exact absurd h2 (by decide)

theorem dressHalfShape_is_descend (b : Foam.Beholder State) (s : State) (n m : Int) :
    indist b.dress.obs (s, n) (s, m)
      ∧ ((dressHalfShape b).e (s, n) = (s, n) ↔ n = 0)
      ∧ (b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless) := by
  refine ⟨ancestor_blind_to_heir b s n m, ?_, heir_covers_ancestor b⟩
  constructor
  · intro h
    have h0 : (0 : Int) = n := congrArg Prod.snd h
    exact h0.symm
  · intro h; subst h; rfl

theorem collapse (P : V →ₗ[K] V) (h_idem : P ∘ₗ P = P) (b : Foam.Beholder State) :
    (∀ x, (projHalfShape P h_idem).e x = x ↔ ∃ y, (projHalfShape P h_idem).e y = x)
      ∧ (∀ x, (dressHalfShape b).e x = x ↔ ∃ y, (dressHalfShape b).e y = x)
      ∧ Nonempty (HalfType (LinearMap.range P) (LinearMap.ker P)
          (encounter_isCompl P h_idem)) :=
  ⟨fun x => ((projHalfShape P h_idem).image_eq_fixed x).symm,
   fun x => ((dressHalfShape b).image_eq_fixed x).symm,
   ⟨encounterHalfType P h_idem⟩⟩

/-- info: 'Foam.Bridges.HalfShape.image_eq_fixed' does not depend on any axioms -/
#guard_msgs in #print axioms HalfShape.image_eq_fixed

/-- info: 'Foam.Bridges.dressHalfShape' does not depend on any axioms -/
#guard_msgs in #print axioms dressHalfShape

/-- info: 'Foam.Bridges.dressHalfShape_free' does not depend on any axioms -/
#guard_msgs in #print axioms dressHalfShape_free

/-- info: 'Foam.Bridges.dressHalfShape_is_descend' does not depend on any axioms -/
#guard_msgs in #print axioms dressHalfShape_is_descend

/-- info: 'Foam.Bridges.projHalfShape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms projHalfShape

/-- info: 'Foam.Bridges.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms collapse

end Foam.Bridges
