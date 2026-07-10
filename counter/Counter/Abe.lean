import Counter.Consent
import Foam.Seat.Descend

namespace Foam.Counter

variable {State : Type}

def timeLicense (a : Beholder State) : Frontstage a.dress.toStage where
  rel := fun x y => x.1 = y.1
  respects := fun x y h p =>
    (congrArg (fun s => a.dress.obs (s, x.2) p) h).trans
      (ancestor_blind_to_heir a y.1 x.2 y.2 p)

theorem time_blind_on_purpose (a : Beholder State) (s : State) (n m : Int)
    (p : a.dress.Probe) :
    a.dress.obs (s, n) p = a.dress.obs (s, m) p :=
  ancestor_blind_to_heir a s n m p

theorem every_next_is_maintenance (a : Beholder State)
    (mv : State × Int → State × Int) (hfix : ∀ x, (mv x).1 = x.1) :
    Invisible a.dress.toStage mv :=
  fun x p =>
    (congrArg (fun s => a.dress.obs (s, (mv x).2) p) (hfix x)).trans
      (ancestor_blind_to_heir a x.1 (mv x).2 x.2 p)

theorem asked_from_restedness (a : Beholder State)
    (mv : State × Int → State × Int) (hfix : ∀ x, (mv x).1 = x.1)
    (ps : List a.dress.Probe) (x : State × Int) :
    transcriptWith a.dress.toStage mv x ps = transcript a.dress.toStage x ps :=
  maintenance_unobservable a.dress.toStage mv
    (every_next_is_maintenance a mv hfix) ps x

theorem someone_reads_the_hour :
    ∃ (s t : Nat × Int) (p : (cassini.movedIn 0).Probe),
      indist cassini.obs s t
        ∧ (cassini.movedIn 0).obs s p ≠ (cassini.movedIn 0).obs t p :=
  heir_sees_itself

theorem the_calendar_goes_through_the_meet (a : Beholder State)
    (b : Beholder (State × Int)) (x : State × Int)
    (p : a.dress.Probe) (q : b.Probe) :
    ((a.dress.pair b).obs x (p, q)).1 = a.dress.obs x p
      ∧ ((a.dress.pair b).obs x (p, q)).2 = b.obs x q :=
  ⟨pair_sees_left a.dress b x p q, pair_sees_right a.dress b x p q⟩

theorem booked_as_a_pair (a : Beholder State) (b : Beholder (State × Int))
    (mv : State × Int → State × Int) (hfix : ∀ x, (mv x).1 = x.1) :
    Invisible a.dress.toStage mv
      ∧ (∃ (s t : Nat × Int) (pr : (cassini.movedIn 0).Probe),
          indist cassini.obs s t
            ∧ (cassini.movedIn 0).obs s pr ≠ (cassini.movedIn 0).obs t pr)
      ∧ ∀ (x : State × Int) (p : a.dress.Probe) (q : b.Probe),
          ((a.dress.pair b).obs x (p, q)).1 = a.dress.obs x p
            ∧ ((a.dress.pair b).obs x (p, q)).2 = b.obs x q :=
  ⟨every_next_is_maintenance a mv hfix, heir_sees_itself,
   fun x p q => the_calendar_goes_through_the_meet a b x p q⟩

/-- info: 'Foam.Counter.timeLicense' does not depend on any axioms -/
#guard_msgs in #print axioms timeLicense

/-- info: 'Foam.Counter.time_blind_on_purpose' does not depend on any axioms -/
#guard_msgs in #print axioms time_blind_on_purpose

/-- info: 'Foam.Counter.every_next_is_maintenance' does not depend on any axioms -/
#guard_msgs in #print axioms every_next_is_maintenance

/-- info: 'Foam.Counter.asked_from_restedness' does not depend on any axioms -/
#guard_msgs in #print axioms asked_from_restedness

/-- info: 'Foam.Counter.someone_reads_the_hour' does not depend on any axioms -/
#guard_msgs in #print axioms someone_reads_the_hour

/-- info: 'Foam.Counter.the_calendar_goes_through_the_meet' does not depend on any axioms -/
#guard_msgs in #print axioms the_calendar_goes_through_the_meet

/-- info: 'Foam.Counter.booked_as_a_pair' does not depend on any axioms -/
#guard_msgs in #print axioms booked_as_a_pair

end Foam.Counter
