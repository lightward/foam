import Foam.Seat.Clock
import Foam.Platonism.Tower

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem t447 (S : Ty16 G) (o : S.Ty24) (p : S.Ty24) :
    (S.d214 o).d049 ((S.d214 o).d051 p) = p :=
  (S.d214 o).t145 p

theorem t449 (S : Ty16 G) (o : S.Ty24) (g : G) (p : S.Ty24) :
    (S.d214 o).d051 (S.d131 g p) = g * (S.d214 o).d051 p :=
  S.t437 g p o

theorem t448 (S : Ty16 G) (o o' : S.Ty24) (p : S.Ty24) :
    (S.d214 o).d051 p = (S.d214 o').d051 p * S.d133 o' o :=
  S.t436 o o' p

theorem t459 (S : Ty16 G) (o o' : S.Ty24) (h : o ≠ o') :
    ∃ p, (S.d214 o).d051 p ≠ (S.d214 o').d051 p :=
  S.t438 o o' h

theorem t450 (S : Ty16 G) (o : S.Ty24) :
    (∀ p, (S.d214 o).d049 ((S.d214 o).d051 p) = p)
      ∧ (∀ g p, (S.d214 o).d051 (S.d131 g p) = g * (S.d214 o).d051 p)
      ∧ (∀ o' p, (S.d214 o).d051 p = (S.d214 o').d051 p * S.d133 o' o)
      ∧ (∀ o', o ≠ o' → ∃ p, (S.d214 o).d051 p ≠ (S.d214 o').d051 p) :=
  ⟨fun p => t447 S o p, fun g p => t449 S o g p,
   fun o' p => t448 S o o' p, fun o' h => t459 S o o' h⟩

theorem t446 (o : d222.Ty24) :
    (∀ p, (d222.d214 o).d049 ((d222.d214 o).d051 p) = p)
      ∧ (∀ g p, (d222.d214 o).d051 (d222.d131 g p) = g * (d222.d214 o).d051 p) :=
  ⟨fun p => t447 d222 o p, fun g p => t449 d222 o g p⟩

theorem t107 : t067 3 ∧ ¬ t067 4 :=
  t105

/-- info: 'Foam.t447' does not depend on any axioms -/
#guard_msgs in #print axioms t447

/-- info: 'Foam.t449' does not depend on any axioms -/
#guard_msgs in #print axioms t449

/-- info: 'Foam.t448' does not depend on any axioms -/
#guard_msgs in #print axioms t448

/-- info: 'Foam.t459' does not depend on any axioms -/
#guard_msgs in #print axioms t459

/-- info: 'Foam.t450' does not depend on any axioms -/
#guard_msgs in #print axioms t450

/-- info: 'Foam.t446' does not depend on any axioms -/
#guard_msgs in #print axioms t446

/-- info: 'Foam.t107' does not depend on any axioms -/
#guard_msgs in #print axioms t107

end Foam
