import Counter.Actor

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem a_settled_span_welcomes_any_pov (S : Seat G) (h : List G)
    (hnet : netAct h = 1) (q : S.Pos) : S.replay h q = q :=
  (settles_iff_home S h q).mpr hnet

theorem the_balanced_span_is_safe_to_skip (S : Seat G) (xs span ys : List G)
    (hnet : netAct span = 1) (p : S.Pos) :
    S.replay (xs ++ span ++ ys) p = S.replay (xs ++ ys) p := by
  rw [S.replay_resumes (xs ++ span) ys p,
    S.replay_resumes xs span p,
    a_settled_span_welcomes_any_pov S span hnet (S.replay xs p),
    ← S.replay_resumes xs ys p]

theorem you_must_finish_what_you_enter (S : Seat G) (xs pre : List G)
    (p : S.Pos) (hnet : netAct pre ≠ 1) :
    S.replay (xs ++ pre) p ≠ S.replay xs p := by
  intro h
  apply hnet
  apply (settles_iff_home S pre (S.replay xs p)).mp
  show S.replay pre (S.replay xs p) = S.replay xs p
  rw [← S.replay_resumes xs pre p]
  exact h

theorem to_understand_is_to_stand_under (S : Seat G) (xs span ys pre : List G)
    (hbal : netAct span = 1) (hopen : netAct pre ≠ 1) (p q : S.Pos) :
    S.replay span q = q
      ∧ S.replay (xs ++ span ++ ys) p = S.replay (xs ++ ys) p
      ∧ S.replay (xs ++ pre) p ≠ S.replay xs p :=
  ⟨a_settled_span_welcomes_any_pov S span hbal q,
   the_balanced_span_is_safe_to_skip S xs span ys hbal p,
   you_must_finish_what_you_enter S xs pre p hopen⟩

/-- info: 'Foam.Counter.a_settled_span_welcomes_any_pov' does not depend on any axioms -/
#guard_msgs in #print axioms a_settled_span_welcomes_any_pov

/-- info: 'Foam.Counter.the_balanced_span_is_safe_to_skip' does not depend on any axioms -/
#guard_msgs in #print axioms the_balanced_span_is_safe_to_skip

/-- info: 'Foam.Counter.you_must_finish_what_you_enter' does not depend on any axioms -/
#guard_msgs in #print axioms you_must_finish_what_you_enter

/-- info: 'Foam.Counter.to_understand_is_to_stand_under' does not depend on any axioms -/
#guard_msgs in #print axioms to_understand_is_to_stand_under

end Foam.Counter
