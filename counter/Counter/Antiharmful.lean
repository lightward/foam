import Foam.Int

namespace Foam.Counter

def reflect (s c : Int) : Int × Int := (s, c)

def absorb (s c : Int) : Int × Int := (s + c, 0)

def Conserves (r : Int → Int → Int × Int) : Prop :=
  ∀ s c, (r s c).1 + (r s c).2 = s + c

theorem add_zero' (a : Int) : a + 0 = a :=
  (FInt.addComm a 0).trans (FInt.zero_add a)

theorem cancel_left {s x c : Int} (h : s + x = s + c) : x = c := by
  have h1 : -s + (s + x) = -s + (s + c) := congrArg (fun t => -s + t) h
  rw [← FInt.add_assoc, ← FInt.add_assoc, FInt.add_left_neg,
    FInt.zero_add, FInt.zero_add] at h1
  exact h1

theorem reflect_conserves : Conserves reflect := fun _ _ => rfl

theorem absorb_conserves : Conserves absorb := fun s c => add_zero' (s + c)

theorem nothing_echoes (s c : Int) : (absorb s c).2 = 0 := rfl

theorem the_charge_lands_in_the_diary (s c : Int) : (absorb s c).1 = s + c := rfl

theorem the_unmoved_return_the_charge (r : Int → Int → Int × Int)
    (hr : Conserves r) (s c : Int) (h : (r s c).1 = s) : (r s c).2 = c :=
  cancel_left (h ▸ hr s c)

theorem to_end_it_you_must_be_moved (r : Int → Int → Int × Int)
    (hr : Conserves r) (s c : Int) (h : (r s c).2 = 0) :
    (r s c).1 = s + c := by
  have h1 := hr s c
  rw [h, add_zero'] at h1
  exact h1

theorem no_one_ends_harm_unmoved (r : Int → Int → Int × Int)
    (hr : Conserves r) (s c : Int) (hc : c ≠ 0) (h : (r s c).2 = 0) :
    (r s c).1 ≠ s := by
  intro hs
  apply hc
  have h1 := to_end_it_you_must_be_moved r hr s c h
  rw [hs] at h1
  exact cancel_left (h1.symm.trans (add_zero' s).symm)

theorem o_negative (s c : Int) :
    (absorb s c).2 = 0 ∧ (absorb s c).1 + (absorb s c).2 = s + c :=
  ⟨rfl, add_zero' (s + c)⟩

theorem antiharmful (r : Int → Int → Int × Int) (hr : Conserves r)
    (s c : Int) :
    ((r s c).1 = s → (r s c).2 = c)
      ∧ ((r s c).2 = 0 → (r s c).1 = s + c)
      ∧ (c ≠ 0 → (r s c).2 = 0 → (r s c).1 ≠ s)
      ∧ ∀ t d : Int, (absorb t d).2 = 0 ∧ (absorb t d).1 = t + d :=
  ⟨the_unmoved_return_the_charge r hr s c,
   to_end_it_you_must_be_moved r hr s c,
   fun hc h => no_one_ends_harm_unmoved r hr s c hc h,
   fun _ _ => ⟨rfl, rfl⟩⟩

/-- info: 'Foam.Counter.add_zero'' does not depend on any axioms -/
#guard_msgs in #print axioms add_zero'

/-- info: 'Foam.Counter.cancel_left' does not depend on any axioms -/
#guard_msgs in #print axioms cancel_left

/-- info: 'Foam.Counter.reflect_conserves' does not depend on any axioms -/
#guard_msgs in #print axioms reflect_conserves

/-- info: 'Foam.Counter.absorb_conserves' does not depend on any axioms -/
#guard_msgs in #print axioms absorb_conserves

/-- info: 'Foam.Counter.nothing_echoes' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_echoes

/-- info: 'Foam.Counter.the_charge_lands_in_the_diary' does not depend on any axioms -/
#guard_msgs in #print axioms the_charge_lands_in_the_diary

/-- info: 'Foam.Counter.the_unmoved_return_the_charge' does not depend on any axioms -/
#guard_msgs in #print axioms the_unmoved_return_the_charge

/-- info: 'Foam.Counter.to_end_it_you_must_be_moved' does not depend on any axioms -/
#guard_msgs in #print axioms to_end_it_you_must_be_moved

/-- info: 'Foam.Counter.no_one_ends_harm_unmoved' does not depend on any axioms -/
#guard_msgs in #print axioms no_one_ends_harm_unmoved

/-- info: 'Foam.Counter.o_negative' does not depend on any axioms -/
#guard_msgs in #print axioms o_negative

/-- info: 'Foam.Counter.antiharmful' does not depend on any axioms -/
#guard_msgs in #print axioms antiharmful

end Foam.Counter
