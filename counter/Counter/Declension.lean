import Counter.Authority

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem nominative_unmarked (S : Seat G) (o : S.Pos) :
    (S.chart o).fwd o = 1 :=
  S.sub_self o

theorem declension_is_regular (S : Seat G) (o o' : S.Pos) (p : S.Pos) :
    (S.chart o).fwd p = (S.chart o').fwd p * rebase S o o' :=
  S.change_of_frame o o' p

/-- info: 'Foam.Counter.nominative_unmarked' does not depend on any axioms -/
#guard_msgs in #print axioms nominative_unmarked

/-- info: 'Foam.Counter.declension_is_regular' does not depend on any axioms -/
#guard_msgs in #print axioms declension_is_regular

end Foam.Counter
