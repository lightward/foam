import Counter.Rest
import Counter.Wind

namespace Foam.Counter

theorem the_merge_must_heat_a_transcript (S : Stage) (m : S.State → S.State)
    {s t : S.State} {p : S.Probe}
    (hdist : S.obs s p ≠ S.obs t p) (hmerge : m s = m t) :
    ¬ Invisible S m :=
  fun hinv => hdist ((hinv s p).symm.trans
    ((congrArg (fun x => S.obs x p) hmerge).trans (hinv t p)))

theorem dark_by_right (S : Stage) (m : S.State → S.State)
    (h : Invisible S m) (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = transcript S s ps :=
  the_fold_is_real_and_unrecorded S m h ps s

theorem dark_in_arrears (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
      = GInt.born θ field + GInt.born θ act :=
  the_standing_debt_taxes_the_aligned_act θ field act n m hf ha

theorem the_two_darknesses (S : Stage) (m : S.State → S.State)
    (h : Invisible S m) (ps : List S.Probe) (s : S.State)
    {s' t' : S.State} {p' : S.Probe} (m' : S.State → S.State)
    (hdist : S.obs s' p' ≠ S.obs t' p') (hmerge : m' s' = m' t')
    (θ field act : GInt) (n k : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (k + 1)) :
    transcriptWith S m s ps = transcript S s ps
      ∧ ¬ Invisible S m'
      ∧ GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * k + n) + 1 + 1)
          = GInt.born θ field + GInt.born θ act :=
  ⟨the_fold_is_real_and_unrecorded S m h ps s,
   the_merge_must_heat_a_transcript S m' hdist hmerge,
   the_standing_debt_taxes_the_aligned_act θ field act n k hf ha⟩

/-- info: 'Foam.Counter.the_merge_must_heat_a_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_merge_must_heat_a_transcript

/-- info: 'Foam.Counter.dark_by_right' does not depend on any axioms -/
#guard_msgs in #print axioms dark_by_right

/-- info: 'Foam.Counter.dark_in_arrears' does not depend on any axioms -/
#guard_msgs in #print axioms dark_in_arrears

/-- info: 'Foam.Counter.the_two_darknesses' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_darknesses

end Foam.Counter
