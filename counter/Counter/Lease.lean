import Foam.Seat.Stage
import Foam.Bubble
import Counter.Ground

namespace Foam.Counter

def Ground {S : Type} (P : S → S) : Prop := ∀ s, P (P s) = P s

variable {S : Type}

theorem the_lease_is_the_wall {W : Stage} (P n : W.State → W.State) :
    (∀ w, P (n w) = P w) ↔ (groundBubble W P).FixesWall n :=
  Iff.rfl

theorem exchanged_grounds_compose (P Q : S → S)
    (hP : Ground P) (hQ : Ground Q) (hx : ∀ s, P (Q s) = Q (P s)) :
    Ground (fun s => P (Q s)) := by
  intro s
  show P (Q (P (Q s))) = P (Q s)
  have e : Q (P (Q s)) = P (Q s) := by
    rw [← hx (Q s)]
    exact congrArg P (hQ s)
  rw [e]
  exact hP (Q s)

theorem no_form_signed_once :
    ∃ P Q : Option Bool → Option Bool,
      Ground P ∧ Ground Q ∧ ¬ Ground (fun x => P (Q x)) :=
  ⟨fun x => match x with | some true => some false | some false => some false | none => none,
   fun x => match x with | some false => none | some true => some true | none => none,
   fun s => match s with | some true => rfl | some false => rfl | none => rfl,
   fun s => match s with | some true => rfl | some false => rfl | none => rfl,
   fun h => nomatch h (some true)⟩

theorem respectful_arrivals_renew_for_free (P n : S → S)
    (hP : Ground P) (hn : ∀ s, P (n s) = P s) :
    Ground (fun s => P (n s)) := by
  intro s
  show P (n (P (n s))) = P (n s)
  rw [hn (P (n s)), hP (n s)]

theorem the_lease (W : Stage) (P n : W.State → W.State) :
    ((∀ w, P (n w) = P w) ↔ (groundBubble W P).FixesWall n)
      ∧ (∀ (T : Type) (R Q : T → T), Ground R → Ground Q →
          (∀ s, R (Q s) = Q (R s)) → Ground (fun s => R (Q s)))
      ∧ (∃ R Q : Option Bool → Option Bool,
          Ground R ∧ Ground Q ∧ ¬ Ground (fun x => R (Q x)))
      ∧ ∀ (T : Type) (R m : T → T), Ground R → (∀ s, R (m s) = R s) →
          Ground (fun s => R (m s)) :=
  ⟨the_lease_is_the_wall P n,
   fun _ R Q hR hQ hx => exchanged_grounds_compose R Q hR hQ hx,
   no_form_signed_once,
   fun _ R m hR hm => respectful_arrivals_renew_for_free R m hR hm⟩

/-- info: 'Foam.Counter.the_lease_is_the_wall' does not depend on any axioms -/
#guard_msgs in #print axioms the_lease_is_the_wall

/-- info: 'Foam.Counter.exchanged_grounds_compose' does not depend on any axioms -/
#guard_msgs in #print axioms exchanged_grounds_compose

/-- info: 'Foam.Counter.no_form_signed_once' does not depend on any axioms -/
#guard_msgs in #print axioms no_form_signed_once

/-- info: 'Foam.Counter.respectful_arrivals_renew_for_free' does not depend on any axioms -/
#guard_msgs in #print axioms respectful_arrivals_renew_for_free

/-- info: 'Foam.Counter.the_lease' does not depend on any axioms -/
#guard_msgs in #print axioms the_lease

end Foam.Counter
