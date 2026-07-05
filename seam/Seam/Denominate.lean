import Foam.Ledger
import Foam.Seat.Signed

namespace Foam.Bridges

def SameTender {Src B : Type} [DecidableEq B] (l l' : List (Src × B)) : Prop :=
  ∀ b, Foam.Ledger.freq (unsign l) b = Foam.Ledger.freq (unsign l') b

def Money (Src B : Type) [DecidableEq B] : Type :=
  Quot (SameTender (Src := Src) (B := B))

theorem any_speaker_same_tender {Src B : Type} [DecidableEq B] (s t : Src)
    (v : List B) : SameTender (sign s v) (sign t v) := by
  intro b
  rw [voice_survives_signing, voice_survives_signing]

theorem the_record_keeps_the_creditor {Src B : Type} (s t : Src) (b : B)
    (v : List B) (h : sign s (b :: v) = sign t (b :: v)) : s = t :=
  sign_faithful s t b v h

theorem same_tender_different_stories :
    SameTender (sign true [true]) (sign false [true])
      ∧ sign true [true] ≠ sign false [true] :=
  ⟨any_speaker_same_tender true false [true], by decide⟩

theorem money_forgets_the_speaker {Src B : Type} [DecidableEq B] (s t : Src)
    (v : List B) :
    Quot.mk SameTender (sign s v) = Quot.mk SameTender (sign t v) :=
  Quot.sound (any_speaker_same_tender s t v)

theorem no_refund_of_attribution :
    ¬ ∃ g : Money Bool Bool → List (Bool × Bool),
        ∀ l, g (Quot.mk SameTender l) = l := by
  rintro ⟨g, hg⟩
  have e := congrArg g (money_forgets_the_speaker true false [true])
  rw [hg, hg] at e
  exact absurd e (by decide)

theorem denomination {Src B : Type} [DecidableEq B] (s t : Src) (v : List B)
    (b : B) (w : List B) (hst : sign s (b :: w) = sign t (b :: w)) :
    SameTender (sign s v) (sign t v)
      ∧ s = t
      ∧ (Quot.mk SameTender (sign s v) = Quot.mk SameTender (sign t v))
      ∧ ¬ ∃ g : Money Bool Bool → List (Bool × Bool),
            ∀ l, g (Quot.mk SameTender l) = l :=
  ⟨any_speaker_same_tender s t v,
   sign_faithful s t b w hst,
   money_forgets_the_speaker s t v,
   no_refund_of_attribution⟩

/-- info: 'Foam.Bridges.any_speaker_same_tender' does not depend on any axioms -/
#guard_msgs in #print axioms any_speaker_same_tender

/-- info: 'Foam.Bridges.the_record_keeps_the_creditor' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_keeps_the_creditor

/-- info: 'Foam.Bridges.same_tender_different_stories' does not depend on any axioms -/
#guard_msgs in #print axioms same_tender_different_stories

/-- info: 'Foam.Bridges.money_forgets_the_speaker' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms money_forgets_the_speaker

/-- info: 'Foam.Bridges.no_refund_of_attribution' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms no_refund_of_attribution

/-- info: 'Foam.Bridges.denomination' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms denomination

end Foam.Bridges
