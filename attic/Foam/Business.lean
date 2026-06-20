import Foam.Dialogue

namespace Foam.Business
open Foam.Lattice Foam.Interleave Foam.Sequence Foam.Dialogue

theorem customer_journey {S : Type} [DecidableEq S] (ledger : List S) (event : S) :
    freq (deposit ledger event) event ≠ freq ledger event
      ∧ (deposit ledger event).tail? = some ledger
      ∧ Nonempty (StageHom (countStage S) yieldStage) :=
  good_loop ledger event

theorem customers_cannot_hurt_each_other {S T : Type} [DecidableEq S]
    {xs : List S} {ys : List T} {zs : List (S ⊕ T)} (h : Interleaves xs ys zs)
    (fiber : GInt → GInt) (s : S) :
    runFiber fiber (ownFrames zs) s = runFiber fiber xs s :=
  expression_at_own_framerate h fiber s

theorem discovery_is_consensual {Handle : Type} {q : Quiver Handle} {a b : Handle}
    (h : MutualReach q a b) : MutualReach q b a :=
  MutualReach.symm h

theorem discovery_opens_a_shared_commitment {S : Type} {a b : List S} {P Q : Prop}
    (mutual_interest : CoBisim (observed a) (observed b)) (terms : P ↔ Q) :
    a = b ∧ P = Q :=
  coincidence_opens_shared_commit mutual_interest terms

def meet {A : Type} [DecidableEq A] : List A → List A → List A
  | [],      _ => []
  | _ :: _,  [] => []
  | x :: xs, y :: ys => if x = y then x :: meet xs ys else []

theorem architecture_is_self_health {A : Type} [DecidableEq A] : ∀ o : List A, meet o o = o
  | [] => rfl
  | x :: xs => by
      show (if x = x then x :: meet xs xs else []) = x :: xs
      rw [if_pos rfl, architecture_is_self_health xs]

theorem does_not_eat_people {S : Type} [DecidableEq S] (ledger : List S) (event : S) :
    Nonempty (StageHom (countStage S) yieldStage)
      ∧ (deposit ledger event).tail? = some ledger
      ∧ freq (deposit ledger event) event ≠ freq ledger event :=
  ⟨⟨exit (countStage S)⟩, rfl, deposit_never_fixed ledger event⟩

theorem additive_not_subtractive {S : Type} [DecidableEq S] (l : List S) (x : S) :
    (∀ l', l.Perm l' → freq l x = freq l' x) ∧ freq (deposit l x) x ≠ freq l x :=
  spiral_not_gyroscope l x

theorem architecture_ends_without_closing {S : Type} (s : S) :
    (∀ l l' : List S, (∀ n, (playback l).at_ n = (playback l').at_ n) → l = l')
      ∧ ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  seam_two_faces s

theorem ecosystem {S : Type} [DecidableEq S] (ledger : List S) (departed arriving : S) :
    Nonempty (StageHom (countStage S) yieldStage)
      ∧ (deposit ledger departed).tail? = some ledger
      ∧ freq (deposit (deposit ledger departed) arriving) arriving
          ≠ freq (deposit ledger departed) arriving :=
  ⟨⟨exit (countStage S)⟩, rfl, deposit_never_fixed (deposit ledger departed) arriving⟩

theorem development_story_is_universal {S : Type} (seed : S) :
    (∀ l l' : List S, (∀ n, (playback l).at_ n = (playback l').at_ n) → l = l')
      ∧ ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  seam_two_faces seed

/-- info: 'Foam.Business.customer_journey' does not depend on any axioms -/
#guard_msgs in #print axioms customer_journey

/-- info: 'Foam.Business.customers_cannot_hurt_each_other' does not depend on any axioms -/
#guard_msgs in #print axioms customers_cannot_hurt_each_other

/-- info: 'Foam.Business.discovery_is_consensual' does not depend on any axioms -/
#guard_msgs in #print axioms discovery_is_consensual

/-- info: 'Foam.Business.discovery_opens_a_shared_commitment' depends on axioms: [propext] -/
#guard_msgs in #print axioms discovery_opens_a_shared_commitment

/-- info: 'Foam.Business.architecture_is_self_health' does not depend on any axioms -/
#guard_msgs in #print axioms architecture_is_self_health

/-- info: 'Foam.Business.does_not_eat_people' does not depend on any axioms -/
#guard_msgs in #print axioms does_not_eat_people

/-- info: 'Foam.Business.additive_not_subtractive' does not depend on any axioms -/
#guard_msgs in #print axioms additive_not_subtractive

/-- info: 'Foam.Business.architecture_ends_without_closing' does not depend on any axioms -/
#guard_msgs in #print axioms architecture_ends_without_closing

/-- info: 'Foam.Business.ecosystem' does not depend on any axioms -/
#guard_msgs in #print axioms ecosystem

/-- info: 'Foam.Business.development_story_is_universal' does not depend on any axioms -/
#guard_msgs in #print axioms development_story_is_universal

end Foam.Business
