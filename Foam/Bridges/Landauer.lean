import Foam.Maintenance
import Foam.Wedge

namespace Foam.Bridges

theorem merge_never_invisible (S : Stage) (m : S.State → S.State)
    {s t : S.State} {p : S.Probe}
    (hdist : S.obs s p ≠ S.obs t p) (hmerge : m s = m t) :
    ¬ Invisible S m := fun hinv =>
  hdist ((hinv s p).symm.trans
    ((congrArg (fun x => S.obs x p) hmerge).trans (hinv t p)))

theorem invisible_preserves_distinction (S : Stage) (m : S.State → S.State)
    (hinv : Invisible S m) {s t : S.State} {p : S.Probe}
    (hdist : S.obs s p ≠ S.obs t p) : m s ≠ m t :=
  fun hmerge => merge_never_invisible S m hdist hmerge hinv

theorem landauer (S : Stage) (m : S.State → S.State) :
    (∀ s t : S.State, ∀ p : S.Probe,
        S.obs s p ≠ S.obs t p → m s = m t → ¬ Invisible S m)
      ∧ Invisible S (fun s => s)
      ∧ (Invisible S m →
          ∀ (ps : List S.Probe) (s : S.State),
            transcriptWith S m s ps = transcript S s ps) :=
  ⟨fun _ _ _ hdist hmerge => merge_never_invisible S m hdist hmerge,
   invisible_id S,
   fun hinv ps s => maintenance_unobservable S m hinv ps s⟩

/-- info: 'Foam.Bridges.merge_never_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms merge_never_invisible

/-- info: 'Foam.Bridges.invisible_preserves_distinction' does not depend on any axioms -/
#guard_msgs in #print axioms invisible_preserves_distinction

/-- info: 'Foam.Bridges.landauer' does not depend on any axioms -/
#guard_msgs in #print axioms landauer

theorem the_bill_moves_upstairs :
    ∃ ms ms' : List (twoBit.State → twoBit.State),
      ms.length ≠ ms'.length
        ∧ (∀ w p, firstBit.front.obs (enactAll ms w) p
            = firstBit.front.obs (enactAll ms' w) p)
        ∧ ∃ (w : twoBit.State) (pr : twoBit.Probe),
            twoBit.obs (enactAll ms w) pr ≠ twoBit.obs (enactAll ms' w) pr :=
  the_debt_outlives_its_legibility

/-- info: 'Foam.Bridges.the_bill_moves_upstairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_bill_moves_upstairs

end Foam.Bridges
