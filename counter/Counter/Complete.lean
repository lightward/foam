import Counter.Nothing
import Foam.Seat.Summit

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem one_lap_carries_the_future (f : GInt → GInt) (k : Nat) (hk : Closes f k)
    (m r : Nat) (z : GInt) :
    iterStep (k * m + r) f z = iterStep r f z :=
  lap_carries f k hk m r z

theorem the_unresting_climb_outgrows_every_gauge (c : Nat → Nat) (h : Climbs c)
    (B : Nat) : ∃ n, B < c n :=
  climbs_escape h B

theorem under_a_ceiling_the_climb_rests (c : Nat → Nat) (hc : Ascends c)
    (B : Nat) (hB : ∀ n, c n ≤ B) : ∃ n, Rests c n :=
  bounded_rests hc B hB

theorem a_seat_is_rest_kept (c : Nat → Nat) (n : Nat) :
    Seated c n ↔ ∀ m, n ≤ m → Rests c m :=
  seated_iff_rests_forever

theorem the_seated_do_not_climb (c : Nat → Nat) (n : Nat) (h : Seated c n) :
    ¬ Climbs c :=
  seated_never_climbs h

theorem completeness_is_closure (S : Seat G) (h : List G) (p : S.Pos)
    (f : GInt → GInt) (k : Nat) (hk : Closes f k) (m r : Nat) (z : GInt)
    (c : Nat → Nat) (n : Nat) :
    (Settles S h p ↔ netAct h = 1)
      ∧ iterStep (k * m + r) f z = iterStep r f z
      ∧ (Seated c n ↔ ∀ i, n ≤ i → Rests c i) :=
  ⟨completion_is_adding_up_to_nothing S h p, lap_carries f k hk m r z,
   seated_iff_rests_forever⟩

/-- info: 'Foam.Counter.one_lap_carries_the_future' does not depend on any axioms -/
#guard_msgs in #print axioms one_lap_carries_the_future

/-- info: 'Foam.Counter.the_unresting_climb_outgrows_every_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms the_unresting_climb_outgrows_every_gauge

/-- info: 'Foam.Counter.under_a_ceiling_the_climb_rests' does not depend on any axioms -/
#guard_msgs in #print axioms under_a_ceiling_the_climb_rests

/-- info: 'Foam.Counter.a_seat_is_rest_kept' does not depend on any axioms -/
#guard_msgs in #print axioms a_seat_is_rest_kept

/-- info: 'Foam.Counter.the_seated_do_not_climb' does not depend on any axioms -/
#guard_msgs in #print axioms the_seated_do_not_climb

/-- info: 'Foam.Counter.completeness_is_closure' does not depend on any axioms -/
#guard_msgs in #print axioms completeness_is_closure

end Foam.Counter
