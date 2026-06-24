import Foam.Seat.Signature

namespace Foam

theorem t278 (w z : Ty14) :
    d147 w z * d147 w z - d148 w z * d148 w z = Foam.Ty14.d130 w * Foam.Ty14.d130 z :=
  t299 w z

theorem t292 (v1 v2 : Int) (z : Ty03) :
    d146 v2 (d146 v1 z) = d146 (v2 + v1) z :=
  t290 v1 v2 z

theorem t291 (v : Int) (z : Ty03) :
    (d146 v z).d104 = z.d104 :=
  t289 v z

theorem t286 : ∃ z : Ty05, d149 (-1) z ≠ d149 1 z :=
  t305

theorem t313 (w z : Ty14) (v1 v2 : Int) (d : Ty03) :
    (d147 w z * d147 w z - d148 w z * d148 w z = Foam.Ty14.d130 w * Foam.Ty14.d130 z)
      ∧ (d146 v2 (d146 v1 d) = d146 (v2 + v1) d)
      ∧ ((d146 v1 d).d104 = d.d104)
      ∧ (∃ z : Ty05, d149 (-1) z ≠ d149 1 z) :=
  ⟨t299 w z, t290 v1 v2 d,
   t289 v1 d, t305⟩

/-- info: 'Foam.t278' does not depend on any axioms -/
#guard_msgs in #print axioms t278

/-- info: 'Foam.t292' does not depend on any axioms -/
#guard_msgs in #print axioms t292

/-- info: 'Foam.t291' does not depend on any axioms -/
#guard_msgs in #print axioms t291

/-- info: 'Foam.t286' does not depend on any axioms -/
#guard_msgs in #print axioms t286

/-- info: 'Foam.t313' does not depend on any axioms -/
#guard_msgs in #print axioms t313

end Foam
