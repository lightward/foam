import Counter.Declension

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem the_socket_reads_itself_the_same (S : Seat G) (p : S.Pos) :
    (S.chart p).fwd p = 1 :=
  nominative_unmarked S p

theorem the_occupant_is_one_element (S : Seat G) (h : List G) (p : S.Pos) :
    S.replay h p = S.act (netAct h) p :=
  replay_is_netAct S h p

theorem selves_swap_by_one_act (S : Seat G) (h h' : List G) (p : S.Pos) :
    S.act (rebase S (S.replay h p) (S.replay h' p)) (S.replay h p)
        = S.replay h' p
      ∧ ∀ g : G, S.act g (S.replay h p) = S.replay h' p →
          g = rebase S (S.replay h p) (S.replay h' p) :=
  ⟨rebase_carries S (S.replay h p) (S.replay h' p),
   fun g hg => rebase_unique S (S.replay h p) (S.replay h' p) g hg⟩

theorem the_one (S : Seat G) (h h' : List G) (p : S.Pos) :
    (S.chart p).fwd p = 1
      ∧ S.replay h p = S.act (netAct h) p
      ∧ S.act (rebase S (S.replay h p) (S.replay h' p)) (S.replay h p)
          = S.replay h' p :=
  ⟨nominative_unmarked S p, replay_is_netAct S h p,
   rebase_carries S (S.replay h p) (S.replay h' p)⟩

/-- info: 'Foam.Counter.the_socket_reads_itself_the_same' does not depend on any axioms -/
#guard_msgs in #print axioms the_socket_reads_itself_the_same

/-- info: 'Foam.Counter.the_occupant_is_one_element' does not depend on any axioms -/
#guard_msgs in #print axioms the_occupant_is_one_element

/-- info: 'Foam.Counter.selves_swap_by_one_act' does not depend on any axioms -/
#guard_msgs in #print axioms selves_swap_by_one_act

/-- info: 'Foam.Counter.the_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_one

end Foam.Counter
