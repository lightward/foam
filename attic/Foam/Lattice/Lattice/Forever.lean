import Foam.Lattice.Order

namespace Foam.Lattice

theorem nth_stable {S : Type} : ∀ (l : List S) (n : Nat), nth l n = none → nth l (n + 1) = none
  | [], _, _ => rfl
  | _ :: _, 0, h => nomatch h
  | _ :: l, n + 1, h => nth_stable l n h

theorem nth_length {S : Type} : ∀ l : List S, nth l l.length = none
  | [] => rfl
  | _ :: l => nth_length l

structure CoList (S : Type) where
  at_    : Nat → Option S
  stable : ∀ n, at_ n = none → at_ (n + 1) = none

def playback {S : Type} (l : List S) : CoList S := ⟨nth l, nth_stable l⟩

def forever {S : Type} (s : S) : CoList S := ⟨fun _ => some s, fun _ h => nomatch h⟩

theorem forever_escapes {S : Type} (s : S) (l : List S) :
    ∃ n, (playback l).at_ n ≠ (forever s).at_ n :=
  ⟨l.length, fun h => nomatch (nth_length l).symm.trans h⟩

theorem nth_replicate {S : Type} (s : S) :
    ∀ n k, k < n → nth (List.replicate n s) k = some s
  | 0, k, h => absurd h (Nat.not_lt_zero k)
  | _ + 1, 0, _ => rfl
  | n + 1, k + 1, h => by
      show nth (List.replicate n s) k = some s
      exact nth_replicate s n k (Nat.lt_of_succ_lt_succ h)

theorem sustained_hosting {S : Type} (s : S) :
    (∀ n, ∃ l : List S, ∀ k, k < n → (playback l).at_ k = (forever s).at_ k)
      ∧ ¬ ∃ l : List S, ∀ k, (playback l).at_ k = (forever s).at_ k := by
  refine ⟨fun n => ⟨List.replicate n s, fun k hk => nth_replicate s n k hk⟩, ?_⟩
  rintro ⟨l, hl⟩
  obtain ⟨n, hn⟩ := forever_escapes s l
  exact hn (hl n)

/-- info: 'Foam.Lattice.forever_escapes' does not depend on any axioms -/
#guard_msgs in #print axioms forever_escapes

/-- info: 'Foam.Lattice.sustained_hosting' does not depend on any axioms -/
#guard_msgs in #print axioms sustained_hosting

end Foam.Lattice
