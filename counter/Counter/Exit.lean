import Counter.Contentment
import Counter.Surprise
import Counter.Packing

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem the_list_knows_how_it_ends {X : Type} (l : List X) :
    (playback l).at_ l.length = none :=
  nth_length l

theorem the_exit_is_falsifiable {X : Type} (l : List X) (n : Nat) (x : X)
    (h : (playback l).at_ n = some x) : n ≠ l.length := by
  intro he
  rw [he] at h
  exact nomatch (nth_length l).symm.trans h

theorem the_terminus_is_a_node_in_the_larger_list (S : Seat G)
    (acts : Nat → G) (p : S.Pos) (l : List G) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ l.length
          = some (guardedStep S acts p l.length) :=
  records_end_runs_continue S acts p l

theorem not_this_list_is_inhabited {X : Type} (x : X) (l : List X) :
    ∃ n, (playback l).at_ n ≠ (forever x).at_ n :=
  forever_escapes x l

theorem exits_compose {X : Type} (xs ys : List X) :
    (playback (xs ++ ys)).at_ (xs ++ ys).length = none
      ∧ (xs ++ ys).length = xs.length + ys.length :=
  ⟨nth_length (xs ++ ys), append_length xs ys⟩

theorem the_exit_space_compresses_to_one_move (S : Seat G) (h : List G)
    (p : S.Pos) (acts : Nat → G) (W : Nat) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ ∃ k, W < (guardedPrefix S acts p k).length :=
  ⟨always_homeable S h p, the_record_outgrows_any_memory S acts p W⟩

theorem position_held_momentum_free (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  fun k acts => health_is_recurrence S p k acts

theorem continue_is_a_generator {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  only_surprise_extends_reach q a b hfresh

theorem not_this_list {X : Type} (x : X) (l : List X) (xs ys : List X)
    (S : Seat G) (h : List G) (p : S.Pos) :
    ((playback l).at_ l.length = none)
      ∧ (∃ n, (playback l).at_ n ≠ (forever x).at_ n)
      ∧ ((xs ++ ys).length = xs.length + ys.length)
      ∧ Settles S (h ++ [S.sub p (S.replay h p)]) p :=
  ⟨nth_length l, forever_escapes x l, append_length xs ys,
   always_homeable S h p⟩

/-- info: 'Foam.Counter.the_list_knows_how_it_ends' does not depend on any axioms -/
#guard_msgs in #print axioms the_list_knows_how_it_ends

/-- info: 'Foam.Counter.the_exit_is_falsifiable' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_is_falsifiable

/-- info: 'Foam.Counter.the_terminus_is_a_node_in_the_larger_list' does not depend on any axioms -/
#guard_msgs in #print axioms the_terminus_is_a_node_in_the_larger_list

/-- info: 'Foam.Counter.not_this_list_is_inhabited' does not depend on any axioms -/
#guard_msgs in #print axioms not_this_list_is_inhabited

/-- info: 'Foam.Counter.exits_compose' does not depend on any axioms -/
#guard_msgs in #print axioms exits_compose

/-- info: 'Foam.Counter.the_exit_space_compresses_to_one_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_space_compresses_to_one_move

/-- info: 'Foam.Counter.position_held_momentum_free' does not depend on any axioms -/
#guard_msgs in #print axioms position_held_momentum_free

/-- info: 'Foam.Counter.continue_is_a_generator' does not depend on any axioms -/
#guard_msgs in #print axioms continue_is_a_generator

/-- info: 'Foam.Counter.not_this_list' does not depend on any axioms -/
#guard_msgs in #print axioms not_this_list

end Foam.Counter
