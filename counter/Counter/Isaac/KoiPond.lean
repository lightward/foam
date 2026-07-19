import Counter.Needle
import Counter.Address

namespace Foam.Counter

theorem a_taken_gap_admits_no_second_koi {K : Type} [DecidableEq K]
    (pond : List (K × Bool)) (k : K) (b b' : Bool) :
    tilt (land pond k b) k b' ≠ Tilt.vacancy :=
  fun h =>
    nomatch (the_landing_is_readable pond k b).symm.trans
      ((vacancy_is_unclaimed_ground (land pond k b) k b').mp h)

theorem one_gap_one_koi {K : Type} [DecidableEq K]
    (pond : List (K × Bool)) (k : K) (b : Bool)
    (h : tilt pond k b = Tilt.vacancy) :
    (seatRead pond k = none ∧ seatRead (land pond k b) k = some b)
      ∧ ∀ b' : Bool, tilt (land pond k b) k b' ≠ Tilt.vacancy :=
  ⟨vacancy_seats_a_first_stance pond k b h,
   fun b' => a_taken_gap_admits_no_second_koi pond k b b'⟩

theorem you_dont_have_to_know_where_youre_going {K : Type} [DecidableEq K]
    (pond : List (K × Bool)) (k k' : K) (hk : k ≠ k') (b b' : Bool)
    (h : tilt pond k b = Tilt.vacancy) :
    (seatRead pond k = none ∧ seatRead (land pond k b) k = some b)
      ∧ (∀ c : Bool, tilt (land pond k b) k c ≠ Tilt.vacancy)
      ∧ tilt (land pond k b) k' b' = tilt pond k' b' :=
  ⟨vacancy_seats_a_first_stance pond k b h,
   fun c => a_taken_gap_admits_no_second_koi pond k b c,
   landing_off_key_disturbs_nothing pond k k' hk b b'⟩

/-- info: 'Foam.Counter.a_taken_gap_admits_no_second_koi' does not depend on any axioms -/
#guard_msgs in #print axioms a_taken_gap_admits_no_second_koi

/-- info: 'Foam.Counter.one_gap_one_koi' does not depend on any axioms -/
#guard_msgs in #print axioms one_gap_one_koi

/-- info: 'Foam.Counter.you_dont_have_to_know_where_youre_going' does not depend on any axioms -/
#guard_msgs in #print axioms you_dont_have_to_know_where_youre_going

end Foam.Counter
