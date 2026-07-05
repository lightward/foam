import Counter.Circumference
import Counter.Socket
import Counter.Ghost
import Foam.Platonism.Tower

namespace Foam.Counter

theorem torsors_stack {State : Type} (b : Beholder State) (m n : Nat) :
    Rung (n + 1) = (Rung n × Rung n)
      ∧ ((b.flattenN (n + m)).Covers (b.flattenN m)
          ∧ (b.flattenN m).Covers (b.flattenN (n + m))) :=
  ⟨same_stuff_all_the_way_up n, dressN_compose b m n⟩

theorem hops_telescope {G : Type} [Mul G] [One G] (S : Seat G) (p q r : S.Pos) :
    S.sub p q * S.sub q r = S.sub p r :=
  S.path_telescopes p q r

theorem the_word_grows_with_depth {H : Type} (g : H) (L : Nat) :
    (worldline g L).length = L :=
  the_record_grows g L

theorem the_fold_is_one_element_at_any_depth {G : Type} [Mul G] [One G]
    (S : Seat G) (h : List G) (p : S.Pos) :
    S.replay h p = S.act (netAct h) p :=
  replay_is_netAct S h p

theorem re_anchoring_reinflects_the_world {G : Type} [Mul G] [One G]
    (S : Seat G) (o o' p : S.Pos) :
    S.act (rebase S o o') o = o'
      ∧ (S.chart o).fwd p = (S.chart o').fwd p * rebase S o o' :=
  ⟨rebase_carries S o o', declension_is_regular S o o' p⟩

theorem you_cannot_keep_both_anchors {G : Type} [Mul G] [One G]
    (S : Seat G) (o o' : S.Pos) (h : o ≠ o') :
    ∃ p, (S.chart o).fwd p ≠ (S.chart o').fwd p :=
  S.chart_origin_dependent o o' h

theorem recursion_elasticity {G : Type} [Mul G] [One G] (S : Seat G)
    (h : List G) (p : S.Pos) {H : Type} (g : H) (L : Nat) (o o' : S.Pos) :
    (worldline g L).length = L
      ∧ S.replay h p = S.act (netAct h) p
      ∧ S.act (rebase S o o') o = o'
      ∧ ∀ q r s : S.Pos, S.sub q r * S.sub r s = S.sub q s :=
  ⟨the_record_grows g L, replay_is_netAct S h p, rebase_carries S o o',
   fun q r s => S.path_telescopes q r s⟩

/-- info: 'Foam.Counter.torsors_stack' does not depend on any axioms -/
#guard_msgs in #print axioms torsors_stack

/-- info: 'Foam.Counter.hops_telescope' does not depend on any axioms -/
#guard_msgs in #print axioms hops_telescope

/-- info: 'Foam.Counter.the_word_grows_with_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_word_grows_with_depth

/-- info: 'Foam.Counter.the_fold_is_one_element_at_any_depth' does not depend on any axioms -/
#guard_msgs in #print axioms the_fold_is_one_element_at_any_depth

/-- info: 'Foam.Counter.re_anchoring_reinflects_the_world' does not depend on any axioms -/
#guard_msgs in #print axioms re_anchoring_reinflects_the_world

/-- info: 'Foam.Counter.you_cannot_keep_both_anchors' does not depend on any axioms -/
#guard_msgs in #print axioms you_cannot_keep_both_anchors

/-- info: 'Foam.Counter.recursion_elasticity' does not depend on any axioms -/
#guard_msgs in #print axioms recursion_elasticity

end Foam.Counter
