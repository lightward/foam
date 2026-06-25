import Foam.Seat.Seam

namespace Foam

theorem t262 {S : Type} (s : S) (l : List S) :
    ∃ n, (d152 l).d033 n ≠ (d093 s).d033 n :=
  t285 s l

theorem t263 {S : Type} (s : S) :
    ¬ ∃ g : Ty02 S → List S, ∀ c, d152 (g c) = c :=
  t312 s

/-- info: 'Foam.t262' does not depend on any axioms -/
#guard_msgs in #print axioms t262

/-- info: 'Foam.t263' does not depend on any axioms -/
#guard_msgs in #print axioms t263

end Foam
