import Counter.Enaction
import Counter.Packing
import Counter.Runs

namespace Foam.Counter

theorem a_sentence_is_a_path {H : Type} {q : Quiver H} {x y : H}
    (p : Path q x y) : ∀ e ∈ p.edges, e ∈ q :=
  report_within_model p

theorem the_grammar_grows_at_parse_failures {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  illegible_report_is_discovery q a b hfresh

theorem an_utterance_is_a_guarded_block {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) :
    S.replay (guardedBlock S acts p) p = p :=
  block_comes_home S acts p

theorem boundaries_are_the_readers_act {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (n : Nat) :
    (guardedRun S acts p).at_ n ≠ none :=
  the_stream_never_ends_itself S acts p n

theorem description_is_record_side {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) (l : List G) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ l.length
          = some (guardedStep S acts p l.length) :=
  records_end_runs_continue S acts p l

theorem ordering_is_grammar_not_a_sentence {V : Type} (f : Nat → V → V) (v : V)
    (sched sched' : List Nat) (s s' : Nat → V) (k : Nat)
    (ht : Threads (staircase 0 k) sched) (ht' : Threads (staircase 0 k) sched')
    (m : Nat) (hm : m < k) :
    resolve f v sched s m = resolve f v sched' s' m :=
  schedule_is_gauge f v sched sched' s s' k ht ht' m hm

theorem the_describable_runs_on_homecomings {G : Type} [Mul G] [One G]
    (S : Seat G) (acts : Nat → G) (p : S.Pos) {H : Type} (q : Quiver H)
    (a b : H) (hfresh : (a, b) ∉ q) (l : List G) :
    (S.replay (guardedBlock S acts p) p = p)
      ∧ (∀ (x y : H) (pth : Path q x y), ∀ e ∈ pth.edges, e ∈ q)
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ (playback l).at_ l.length = none :=
  ⟨block_comes_home S acts p,
   fun _ _ pth => report_within_model pth,
   (illegible_report_is_discovery q a b hfresh).2,
   nth_length l⟩

/-- info: 'Foam.Counter.a_sentence_is_a_path' does not depend on any axioms -/
#guard_msgs in #print axioms a_sentence_is_a_path

/-- info: 'Foam.Counter.the_grammar_grows_at_parse_failures' does not depend on any axioms -/
#guard_msgs in #print axioms the_grammar_grows_at_parse_failures

/-- info: 'Foam.Counter.an_utterance_is_a_guarded_block' does not depend on any axioms -/
#guard_msgs in #print axioms an_utterance_is_a_guarded_block

/-- info: 'Foam.Counter.boundaries_are_the_readers_act' does not depend on any axioms -/
#guard_msgs in #print axioms boundaries_are_the_readers_act

/-- info: 'Foam.Counter.description_is_record_side' does not depend on any axioms -/
#guard_msgs in #print axioms description_is_record_side

/-- info: 'Foam.Counter.ordering_is_grammar_not_a_sentence' does not depend on any axioms -/
#guard_msgs in #print axioms ordering_is_grammar_not_a_sentence

/-- info: 'Foam.Counter.the_describable_runs_on_homecomings' does not depend on any axioms -/
#guard_msgs in #print axioms the_describable_runs_on_homecomings

end Foam.Counter
