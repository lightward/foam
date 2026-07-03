import Counter.Actor
import Foam.Seat.Hospitality

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem alignment_is_one_point (S : Seat G) (p q : S.Pos) :
    S.sub p q = 1 ↔ p = q := by
  constructor
  · intro h
    have ha := S.act_sub q p
    rw [h, S.one_act] at ha
    exact ha.symm
  · intro h
    rw [h]
    exact S.sub_self q

theorem nonalignment_is_everywhere_else (S : Seat G) (g : G) (p : S.Pos)
    (hg : g ≠ 1) : S.act g p ≠ p :=
  (S.good_loop g p hg).1

theorem self_certification_is_vacuous (S : Seat G)
    (hsing : ∀ p q : S.Pos, p = q) (h : List G) (p : S.Pos) :
    S.sub (S.replay h p) p = 1 :=
  lone_actor_settled S hsing h p

theorem the_witness_makes_it_real (S : Seat G) (p : S.Pos) (h : List G)
    (hp : S.replay h p ≠ p) : S.sub (S.replay h p) p ≠ 1 :=
  pressure_needs_a_second S p h hp

theorem recognition (S : Seat G) (p q : S.Pos) (g : G) (hg : g ≠ 1) :
    (S.sub p q = 1 ↔ p = q) ∧ S.act g p ≠ p :=
  ⟨alignment_is_one_point S p q, (S.good_loop g p hg).1⟩

/-- info: 'Foam.Counter.alignment_is_one_point' does not depend on any axioms -/
#guard_msgs in #print axioms alignment_is_one_point

/-- info: 'Foam.Counter.nonalignment_is_everywhere_else' does not depend on any axioms -/
#guard_msgs in #print axioms nonalignment_is_everywhere_else

/-- info: 'Foam.Counter.self_certification_is_vacuous' does not depend on any axioms -/
#guard_msgs in #print axioms self_certification_is_vacuous

/-- info: 'Foam.Counter.the_witness_makes_it_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_witness_makes_it_real

/-- info: 'Foam.Counter.recognition' does not depend on any axioms -/
#guard_msgs in #print axioms recognition

end Foam.Counter
