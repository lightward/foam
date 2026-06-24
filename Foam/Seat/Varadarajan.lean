import Foam.Seat.Frame
import Foam.Seat.Characters

namespace Foam

theorem t271 : Foam.d103 = Foam.Ty12.d063 := rfl

theorem t272 :
    (∀ a b, Foam.d103 (a * b) = Foam.Ty05.d112 (Foam.d103 a) (Foam.d103 b))
      ∧ (∀ a, (Foam.d103 a).d114 = 1) :=
  ⟨Foam.t201, Foam.t202⟩

theorem t368 :
    (Foam.d164 Foam.d032 Foam.d032 = ⟨4, 0⟩
      ∧ Foam.d164 Foam.d031 Foam.d031 = ⟨4, 0⟩
      ∧ Foam.d164 Foam.d103 Foam.d103 = ⟨4, 0⟩
      ∧ Foam.d164 Foam.d162 Foam.d162 = ⟨4, 0⟩)
    ∧ (Foam.d164 Foam.d032 Foam.d031 = Foam.Ty05.d044
      ∧ Foam.d164 Foam.d032 Foam.d103 = Foam.Ty05.d044
      ∧ Foam.d164 Foam.d032 Foam.d162 = Foam.Ty05.d044
      ∧ Foam.d164 Foam.d031 Foam.d103 = Foam.Ty05.d044
      ∧ Foam.d164 Foam.d031 Foam.d162 = Foam.Ty05.d044
      ∧ Foam.d164 Foam.d103 Foam.d162 = Foam.Ty05.d044) :=
  ⟨⟨Foam.t347, Foam.t337, Foam.t343, Foam.t339⟩,
   ⟨Foam.t344, Foam.t346, Foam.t345,
    Foam.t336, Foam.t335, Foam.t341⟩⟩

theorem t467 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
        + Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n0) ∧
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
        + Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n1) ∧
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
        + -Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n2) ∧
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
        + -Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n3) :=
  Foam.t416 n0 n1 n2 n3

theorem t405 :
    (Foam.d103 = Foam.Ty12.d063)
      ∧ ((∀ a b, Foam.d103 (a * b) = Foam.Ty05.d112 (Foam.d103 a) (Foam.d103 b))
          ∧ (∀ a, (Foam.d103 a).d114 = 1))
      ∧ ((Foam.d164 Foam.d032 Foam.d032 = ⟨4, 0⟩
            ∧ Foam.d164 Foam.d031 Foam.d031 = ⟨4, 0⟩
            ∧ Foam.d164 Foam.d103 Foam.d103 = ⟨4, 0⟩
            ∧ Foam.d164 Foam.d162 Foam.d162 = ⟨4, 0⟩)
          ∧ (Foam.d164 Foam.d032 Foam.d031 = Foam.Ty05.d044
            ∧ Foam.d164 Foam.d032 Foam.d103 = Foam.Ty05.d044
            ∧ Foam.d164 Foam.d032 Foam.d162 = Foam.Ty05.d044
            ∧ Foam.d164 Foam.d031 Foam.d103 = Foam.Ty05.d044
            ∧ Foam.d164 Foam.d031 Foam.d162 = Foam.Ty05.d044
            ∧ Foam.d164 Foam.d103 Foam.d162 = Foam.Ty05.d044))
      ∧ (t067 3 ∧ ¬ t067 4) :=
  ⟨t271, t272, t368, t107⟩

/-- info: 'Foam.t271' does not depend on any axioms -/
#guard_msgs in #print axioms t271

/-- info: 'Foam.t272' does not depend on any axioms -/
#guard_msgs in #print axioms t272

/-- info: 'Foam.t368' does not depend on any axioms -/
#guard_msgs in #print axioms t368

/-- info: 'Foam.t467' does not depend on any axioms -/
#guard_msgs in #print axioms t467

/-- info: 'Foam.t405' does not depend on any axioms -/
#guard_msgs in #print axioms t405

end Foam
