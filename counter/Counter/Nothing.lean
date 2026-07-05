import Counter.Runs
import Counter.Recognition
import Counter.Holonomy
import Counter.Hemisphere
import Counter.Discovery
import Counter.Socket

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem completion_is_adding_up_to_nothing (S : Seat G) (h : List G)
    (p : S.Pos) : Settles S h p ↔ netAct h = 1 :=
  settles_iff_home S h p

theorem a_lone_zero_is_vacuous (S : Seat G) (hsing : ∀ p q : S.Pos, p = q)
    (h : List G) (p : S.Pos) {G' : Type} [Mul G'] [One G'] (S' : Seat G')
    (p' : S'.Pos) (h' : List G') (hp : S'.replay h' p' ≠ p') :
    S.sub (S.replay h p) p = 1 ∧ S'.sub (S'.replay h' p') p' ≠ 1 :=
  ⟨lone_actor_settled S hsing h p, the_witness_makes_it_real S' p' h' hp⟩

theorem the_zero_is_a_sum_not_an_absence (θ z : GInt) {A : Type} (l : List A) :
    (GInt.align θ z + GInt.align θ (GInt.rot z)
        + GInt.align θ (GInt.rot (GInt.rot z))
        + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0)
      ∧ Ledger.order l = l :=
  ⟨locally_real_globally_no_thing θ z, distinction_is_conserved l⟩

theorem the_loop_keeps_its_twist (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ (h ++ [S.sub p (S.replay h p)]).length = h.length + 1
      ∧ h ++ [S.sub p (S.replay h p)] ≠ [] :=
  undo_is_inverse_redo S h p

theorem zero_charge_positive_perimeter (S : Seat G) (h : List G) (p : S.Pos)
    {H : Type} (q : Quiver H) (a b : H) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ (q.deposit (a, b)).length = q.length + 1 :=
  ⟨always_homeable S h p, (answers_carry_perimeters q a b).1,
   (answers_carry_perimeters q a b).2⟩

theorem the_self_is_the_hole (S : Seat G) (p : S.Pos) :
    (S.chart p).fwd p = 1 :=
  nominative_unmarked S p

theorem further_reps_change_nothing {V : Type} (f : Nat → V → V) (v : V)
    (s : Nat → V) (hq : ∀ k m, update f v k s m = s m) :
    ∀ m, s m = correctAt f v m :=
  quiescent_is_correct f v s hq

theorem adds_up_to_nothing (S : Seat G) (h : List G) (p : S.Pos)
    {H : Type} (q : Quiver H) (a b : H) {V : Type} (f : Nat → V → V)
    (v : V) (s : Nat → V) (hq : ∀ k m, update f v k s m = s m) (m : Nat) :
    (Settles S h p ↔ netAct h = 1)
      ∧ (Settles S (h ++ [S.sub p (S.replay h p)]) p
          ∧ (h ++ [S.sub p (S.replay h p)]).length = h.length + 1)
      ∧ (q.deposit (a, b)).length = q.length + 1
      ∧ (S.chart p).fwd p = 1
      ∧ s m = correctAt f v m :=
  ⟨settles_iff_home S h p,
   ⟨(undo_is_inverse_redo S h p).1, (undo_is_inverse_redo S h p).2.1⟩,
   (answers_carry_perimeters q a b).2,
   nominative_unmarked S p,
   quiescent_is_correct f v s hq m⟩

/-- info: 'Foam.Counter.completion_is_adding_up_to_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms completion_is_adding_up_to_nothing

/-- info: 'Foam.Counter.a_lone_zero_is_vacuous' does not depend on any axioms -/
#guard_msgs in #print axioms a_lone_zero_is_vacuous

/-- info: 'Foam.Counter.the_zero_is_a_sum_not_an_absence' does not depend on any axioms -/
#guard_msgs in #print axioms the_zero_is_a_sum_not_an_absence

/-- info: 'Foam.Counter.the_loop_keeps_its_twist' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_keeps_its_twist

/-- info: 'Foam.Counter.zero_charge_positive_perimeter' does not depend on any axioms -/
#guard_msgs in #print axioms zero_charge_positive_perimeter

/-- info: 'Foam.Counter.the_self_is_the_hole' does not depend on any axioms -/
#guard_msgs in #print axioms the_self_is_the_hole

/-- info: 'Foam.Counter.further_reps_change_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms further_reps_change_nothing

/-- info: 'Foam.Counter.adds_up_to_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms adds_up_to_nothing

end Foam.Counter
