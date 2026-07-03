import Counter.Interleave
import Foam.Seat.Epoch

namespace Foam.Counter

def firstSeat (A B : Type) : Beholder (List (A ⊕ B)) :=
  ⟨Unit, List A, fun zs _ => ownFrames zs⟩

def secondSeat (A B : Type) : Beholder (List (A ⊕ B)) :=
  ⟨Unit, List B, fun zs _ => ownFramesR zs⟩

def pairSeat (A B : Type) : Beholder (List (A ⊕ B)) :=
  ⟨Unit, List A × List B, fun zs _ => (ownFrames zs, ownFramesR zs)⟩

def thirdSeat (A B : Type) : Beholder (List (A ⊕ B)) :=
  ⟨Unit, List (A ⊕ B), fun zs _ => zs⟩

theorem third_covers_first (A B : Type) :
    (thirdSeat A B).Covers (firstSeat A B) :=
  ⟨fun u => u, ownFrames, fun _ _ => rfl⟩

theorem third_covers_second (A B : Type) :
    (thirdSeat A B).Covers (secondSeat A B) :=
  ⟨fun u => u, ownFramesR, fun _ _ => rfl⟩

theorem third_covers_the_pair (A B : Type) :
    (thirdSeat A B).Covers (pairSeat A B) :=
  ⟨fun u => u, fun zs => (ownFrames zs, ownFramesR zs), fun _ _ => rfl⟩

theorem pair_blind_to_the_third :
    ¬ (pairSeat Bool Bool).Covers (thirdSeat Bool Bool) := by
  rintro ⟨enc, post, hcov⟩
  have h1 := hcov [Sum.inl true, Sum.inr false] ()
  have h2 := hcov [Sum.inr false, Sum.inl true] ()
  have hne : ([Sum.inl true, Sum.inr false] : List (Bool ⊕ Bool))
      ≠ [Sum.inr false, Sum.inl true] := by decide
  exact absurd (h1.trans h2.symm) hne

def whoActedFirst {A B : Type} : List (A ⊕ B) → Option Bool
  | [] => none
  | Sum.inl _ :: _ => some true
  | Sum.inr _ :: _ => some false

theorem the_third_reads_time :
    ∃ zs zs' : List (Bool ⊕ Bool),
      ownFrames zs = ownFrames zs'
        ∧ ownFramesR zs = ownFramesR zs'
        ∧ whoActedFirst zs ≠ whoActedFirst zs' :=
  ⟨[Sum.inl true, Sum.inr false], [Sum.inr false, Sum.inl true],
   rfl, rfl, by decide⟩

theorem three_suffices {A B X : Type} (f : List (A ⊕ B) → X) :
    ∃ post : List (A ⊕ B) → X,
      ∀ zs, f zs = post ((thirdSeat A B).obs zs ()) :=
  ⟨f, fun _ => rfl⟩

/-- info: 'Foam.Counter.third_covers_first' does not depend on any axioms -/
#guard_msgs in #print axioms third_covers_first

/-- info: 'Foam.Counter.third_covers_second' does not depend on any axioms -/
#guard_msgs in #print axioms third_covers_second

/-- info: 'Foam.Counter.third_covers_the_pair' does not depend on any axioms -/
#guard_msgs in #print axioms third_covers_the_pair

/-- info: 'Foam.Counter.pair_blind_to_the_third' does not depend on any axioms -/
#guard_msgs in #print axioms pair_blind_to_the_third

/-- info: 'Foam.Counter.the_third_reads_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_third_reads_time

/-- info: 'Foam.Counter.three_suffices' does not depend on any axioms -/
#guard_msgs in #print axioms three_suffices

end Foam.Counter
