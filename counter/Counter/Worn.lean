import Counter.Nu

namespace Foam.Counter

theorem materials_wear_out {X : Type} (l : List X) :
    (playback l).at_ l.length = none :=
  nth_length l

theorem mechanisms_wear_in {G : Type} [Mul G] [One G] (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  fun k acts => health_is_recurrence S p k acts

theorem worn {X : Type} (l : List X) {G : Type} [Mul G] [One G]
    (S : Seat G) (p : S.Pos) :
    (playback l).at_ l.length = none
      ∧ ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  ⟨nth_length l, fun k acts => health_is_recurrence S p k acts⟩

/-- info: 'Foam.Counter.materials_wear_out' does not depend on any axioms -/
#guard_msgs in #print axioms materials_wear_out

/-- info: 'Foam.Counter.mechanisms_wear_in' does not depend on any axioms -/
#guard_msgs in #print axioms mechanisms_wear_in

/-- info: 'Foam.Counter.worn' does not depend on any axioms -/
#guard_msgs in #print axioms worn

end Foam.Counter
