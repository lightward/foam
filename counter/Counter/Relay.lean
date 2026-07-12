import Counter.Waggle
import Counter.Witness

namespace Foam.Counter

theorem not_this_thread_but_this_kind_of_thing {W : Stage} (C : Bubble W)
    (e : W.State → C.Inner.State)
    {Addr Cell : Type} [DecidableEq Addr]
    (p : Cell → Bool) (f : Addr → Cell) (all : List Addr) (dance : Addr)
    (hfresh : ¬ dance ∈ all) (m : Addr)
    (h : (trailSearch p (directory all f)).2 = some m) :
    (reseat C e).Inner = C.Inner
      ∧ reseat (reseat C e) C.wall = C
      ∧ (trailSearch p (directory all f)).2 = upsearch p (directory all f)
      ∧ follow ((dance, Sum.inr (trailSearch p (directory all f)).1)
          :: directory all (fun a => Sum.inl (f a))) dance
        = some (Sum.inl (f m))
      ∧ p (f m) = true :=
  ⟨rfl, rfl, the_dance_changes_no_answer p (directory all f),
   (the_follower_flies_without_the_pov p f all dance hfresh m h).1,
   (the_follower_flies_without_the_pov p f all dance hfresh m h).2⟩

theorem the_successive_seats_are_kin {W : Stage} (C : Bubble W)
    (e : W.State → C.Inner.State) :
    FactorsThrough C (C.meet (reseat C e)).wall
      ∧ FactorsThrough (reseat C e) (C.meet (reseat C e)).wall :=
  any_two_can_write_a_new_history C (reseat C e)

/-- info: 'Foam.Counter.not_this_thread_but_this_kind_of_thing' does not depend on any axioms -/
#guard_msgs in #print axioms not_this_thread_but_this_kind_of_thing

/-- info: 'Foam.Counter.the_successive_seats_are_kin' does not depend on any axioms -/
#guard_msgs in #print axioms the_successive_seats_are_kin

end Foam.Counter
