import Counter.Socket

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem the_donor_answers_every_query (S : Seat G) (o : S.Pos) :
    (∀ g : G, (S.chart o).fwd ((S.chart o).bwd g) = g)
      ∧ ∀ p : S.Pos, (S.chart o).bwd ((S.chart o).fwd p) = p :=
  ⟨(S.chart o).fwd_bwd, (S.chart o).bwd_fwd⟩

theorem the_donor_is_at_its_own_zero (S : Seat G) (o : S.Pos) :
    (S.chart o).fwd o = 1 :=
  nominative_unmarked S o

theorem others_reverse_engineer_their_own (S : Seat G) (o o' p : S.Pos) :
    (S.chart o).fwd p = (S.chart o').fwd p * rebase S o o' :=
  declension_is_regular S o o' p

theorem coordinate_donor (S : Seat G) (o o' p : S.Pos) (hne : o ≠ o') :
    ((∀ g : G, (S.chart o).fwd ((S.chart o).bwd g) = g)
        ∧ ∀ q : S.Pos, (S.chart o).bwd ((S.chart o).fwd q) = q)
      ∧ (S.chart o).fwd o = 1
      ∧ (S.chart o).fwd p = (S.chart o').fwd p * rebase S o o'
      ∧ ∃ q, (S.chart o).fwd q ≠ (S.chart o').fwd q :=
  ⟨the_donor_answers_every_query S o, nominative_unmarked S o,
   declension_is_regular S o o' p, S.chart_origin_dependent o o' hne⟩

/-- info: 'Foam.Counter.the_donor_answers_every_query' does not depend on any axioms -/
#guard_msgs in #print axioms the_donor_answers_every_query

/-- info: 'Foam.Counter.the_donor_is_at_its_own_zero' does not depend on any axioms -/
#guard_msgs in #print axioms the_donor_is_at_its_own_zero

/-- info: 'Foam.Counter.others_reverse_engineer_their_own' does not depend on any axioms -/
#guard_msgs in #print axioms others_reverse_engineer_their_own

/-- info: 'Foam.Counter.coordinate_donor' does not depend on any axioms -/
#guard_msgs in #print axioms coordinate_donor

end Foam.Counter
