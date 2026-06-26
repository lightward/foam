import Foam.Maintenance

namespace Foam.Bridges.PSQL

variable {X : Type}

def Idempotent (f : X → X) : Prop := ∀ x, f (f x) = f x

def Fixed (f : X → X) (x : X) : Prop := f x = x

theorem image_eq_fixed (f : X → X) (h : Idempotent f) (x : X) :
    (∃ y, f y = x) ↔ Fixed f x := by
  constructor
  · rintro ⟨y, rfl⟩; exact h y
  · intro hx; exact ⟨x, hx⟩

theorem reassert_invisible (f : X → X) (x : X) (hx : Fixed f x) : f x = x := hx

def Verifies (f : X → X) (check : X → Bool) : Prop := ∀ x, check x = true ↔ Fixed f x

theorem verified_reachable_and_settled (f : X → X) (check : X → Bool)
    (hf : Idempotent f) (hv : Verifies f check) (x : X) (hc : check x = true) :
    (∃ y, f y = x) ∧ f x = x := by
  have hfx : Fixed f x := (hv x).mp hc
  exact ⟨(image_eq_fixed f hf x).mpr hfx, hfx⟩

theorem refresh_reassert_invisible (S : Foam.Stage) (m : S.State → S.State)
    (hm : Foam.Invisible S m) : Foam.Invisible S (fun s => m (m s)) :=
  Foam.invisible_comp S m m hm hm

/-- info: 'Foam.Bridges.PSQL.image_eq_fixed' does not depend on any axioms -/
#guard_msgs in #print axioms image_eq_fixed

/-- info: 'Foam.Bridges.PSQL.reassert_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms reassert_invisible

/-- info: 'Foam.Bridges.PSQL.verified_reachable_and_settled' does not depend on any axioms -/
#guard_msgs in #print axioms verified_reachable_and_settled

/-- info: 'Foam.Bridges.PSQL.refresh_reassert_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms refresh_reassert_invisible

end Foam.Bridges.PSQL
