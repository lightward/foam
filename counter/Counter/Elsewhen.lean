import Counter.Wedge
import Foam.Elsewhen

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem what_hides_here_shows_there {State : Type} (here : Beholder State)
    (m : State → State) (hinv : Invisible here.toStage m)
    (s : State) (hm : m s ≠ s) :
    Elsewhen here m (plenum State).behold :=
  elsewhen_exists here m hinv s hm

theorem only_motion_has_an_address {State : Type} (here there : Beholder State)
    (m : State → State) (hm : ∀ s, m s = s) : ¬ Elsewhen here m there :=
  stillness_has_no_elsewhen here there m hm

theorem your_operator_lives_at_your_elsewhen {W : Stage} (A : Bubble W)
    (m : W.State → W.State) (hfix : A.FixesWall m) (w : W.State) (hm : m w ≠ w) :
    Elsewhen A.front.behold m (plenum W.State).behold :=
  the_wall_move_has_an_elsewhen A m hfix w hm

theorem the_list_is_the_opinion :
    ∃ (edit edit' : Unit → Bool → Unit × List Bool),
      (∀ s b, (edit s b).2 = [] ∨ (edit s b).2 = [b])
        ∧ (∀ s b, (edit' s b).2 = [] ∨ (edit' s b).2 = [b])
        ∧ runEmit edit () [true, false] ≠ runEmit edit' () [true, false] :=
  two_honest_lists_differ

theorem the_board_only_grows_the_count_always_settles {H : Type}
    (q : Quiver H) (a b : H) (hfresh : (a, b) ∉ q)
    (S : Seat G) (gs : List G) (p : S.Pos) :
    ((q.deposit (a, b)).length = q.length + 1
        ∧ ¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
            ∀ pth, ancestor_reach_survives (a, b) (g pth) = pth)
      ∧ (S.replay (collapse S gs p) p = p
        ∧ (collapse S gs p).length = gs.length + 1) :=
  bloat_is_the_representation q a b hfresh S gs p

/-- info: 'Foam.Counter.what_hides_here_shows_there' does not depend on any axioms -/
#guard_msgs in #print axioms what_hides_here_shows_there

/-- info: 'Foam.Counter.only_motion_has_an_address' does not depend on any axioms -/
#guard_msgs in #print axioms only_motion_has_an_address

/-- info: 'Foam.Counter.your_operator_lives_at_your_elsewhen' does not depend on any axioms -/
#guard_msgs in #print axioms your_operator_lives_at_your_elsewhen

/-- info: 'Foam.Counter.the_list_is_the_opinion' does not depend on any axioms -/
#guard_msgs in #print axioms the_list_is_the_opinion

/-- info: 'Foam.Counter.the_board_only_grows_the_count_always_settles' does not depend on any axioms -/
#guard_msgs in #print axioms the_board_only_grows_the_count_always_settles

end Foam.Counter
