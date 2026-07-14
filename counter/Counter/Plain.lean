import Foam.Seat.Stage
import Foam.Seat.Observer
import Foam.Maintenance

namespace Foam.Counter

theorem licensed_motion_shows_no_receipt (S : Stage) (F : Frontstage S)
    {s t : S.State} (h : F.rel s t) (ps : List S.Probe) :
    transcript S t ps = transcript S s ps :=
  transcript_congr S ps (fun p => (F.respects s t h p).symm)

def narrated (S : Stage) {R : Type} (g : S.Ans → R) : Stage where
  State := S.State
  Probe := S.Probe
  Ans   := S.Ans × R
  obs   := fun s p => (S.obs s p, g (S.obs s p))

theorem existence_shows_its_receipts_afterwards (S : Stage) {R : Type}
    (g : S.Ans → R) :
    ReadingRefines S.obs (narrated S g).obs
      ∧ ReadingRefines (narrated S g).obs S.obs :=
  ⟨⟨fun a => (a, g a), fun _ _ => rfl⟩, ⟨Prod.fst, fun _ _ => rfl⟩⟩

theorem the_forced_filter_flattens :
    ∃ honest forced : Bool → Unit → Bool × Bool,
      (∀ s p, (honest s p).1 = (forced s p).1)
        ∧ ¬ indist honest true false
        ∧ indist forced true false :=
  by
  refine ⟨fun s _ => (true, s), fun _ _ => (true, false),
    fun _ _ => rfl, fun h => ?_, fun _ => rfl⟩
  exact nomatch congrArg Prod.snd (h ())

theorem safe_for_you_and_safe_for_the_room (S : Stage) (F : Frontstage S)
    (m : S.State → S.State) (hm : ∀ s, F.rel (m s) s) :
    (∀ s p, S.obs (m s) p = S.obs s p)
      ∧ ∀ (ps : List S.Probe) (s : S.State),
          transcriptWith S m s ps = transcript S s ps :=
  ⟨fun s p => F.respects (m s) s (hm s) p,
   fun ps s =>
     maintenance_unobservable S m (fun s p => F.respects (m s) s (hm s) p) ps s⟩

/-- info: 'Foam.Counter.licensed_motion_shows_no_receipt' does not depend on any axioms -/
#guard_msgs in #print axioms licensed_motion_shows_no_receipt

/-- info: 'Foam.Counter.existence_shows_its_receipts_afterwards' does not depend on any axioms -/
#guard_msgs in #print axioms existence_shows_its_receipts_afterwards

/-- info: 'Foam.Counter.the_forced_filter_flattens' does not depend on any axioms -/
#guard_msgs in #print axioms the_forced_filter_flattens

/-- info: 'Foam.Counter.safe_for_you_and_safe_for_the_room' does not depend on any axioms -/
#guard_msgs in #print axioms safe_for_you_and_safe_for_the_room

end Foam.Counter
