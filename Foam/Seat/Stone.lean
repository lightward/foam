import Foam.Seat.Noether

namespace Foam

theorem t196 (m n : Nat) (z : Ty05) :
    d098 m (d098 n z) = d098 (m + n) z :=
  t186 m n z

theorem t326 (n : Nat) (z : Ty05) : (d098 n z).d114 = z.d114 :=
  t317 n z

theorem t325 (m n : Nat) (z : Ty05) :
    (d098 m (d098 n z) = d098 (m + n) z)
      ∧ ((d098 n z).d114 = z.d114)
      ∧ (d098 4 z = z) :=
  ⟨t186 m n z, t317 n z, t187 z⟩

/-- info: 'Foam.t196' does not depend on any axioms -/
#guard_msgs in #print axioms t196

/-- info: 'Foam.t326' does not depend on any axioms -/
#guard_msgs in #print axioms t326

/-- info: 'Foam.t325' does not depend on any axioms -/
#guard_msgs in #print axioms t325

end Foam
