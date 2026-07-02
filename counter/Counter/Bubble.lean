import Counter.Actor
import Counter.Interleave

namespace Foam.Counter

variable {A B : Type}

theorem freq_ne_zero_mem [DecidableEq A] :
    ∀ (l : List A) (a : A), Ledger.freq l a ≠ 0 → a ∈ l
  | [], _, h => absurd rfl h
  | x :: l, a, h => by
    by_cases hx : x = a
    · rw [hx]; exact List.Mem.head l
    · have hf : Ledger.freq (x :: l) a = Ledger.freq l a := by
        show (if x = a then 1 else 0) + Ledger.freq l a = Ledger.freq l a
        rw [if_neg hx, Nat.zero_add]
      exact List.Mem.tail x (freq_ne_zero_mem l a (fun hz => h (hf.trans hz)))

theorem wound_act_is_own [DecidableEq A] {xs : List A} {ys : List B}
    {zs : List (A ⊕ B)} (h : Interleaves xs ys zs) (a : A)
    (hw : Ledger.freq (ownFrames zs) a ≠ 0) : a ∈ xs := by
  rw [own_frames_whole h] at hw
  exact freq_ne_zero_mem xs a hw

theorem other_view_unmoved {xs xs' : List A} {ys : List B}
    {zs zs' : List (A ⊕ B)}
    (h : Interleaves xs ys zs) (h' : Interleaves xs' ys zs') :
    ownFramesR zs = ownFramesR zs' :=
  (own_framesR_whole h).trans (own_framesR_whole h').symm

variable {H : Type} [Mul H] [One H]

theorem settles_readthrough (S : Seat H) (p : S.Pos) {xs : List A} {ys : List H}
    {zs : List (A ⊕ H)} (h : Interleaves xs ys zs) :
    Settles S (ownFramesR zs) p ↔ netAct ys = 1 := by
  rw [own_framesR_whole h]
  exact settles_iff_home S ys p

theorem no_cross_drain (S : Seat H) (p : S.Pos) {xs xs' : List A} {ys : List H}
    {zs zs' : List (A ⊕ H)}
    (h : Interleaves xs ys zs) (h' : Interleaves xs' ys zs') :
    Settles S (ownFramesR zs) p ↔ Settles S (ownFramesR zs') p := by
  rw [other_view_unmoved h h']

theorem real_yet_unfelt :
    ∃ zs zs' : List (Bool ⊕ Bool),
      zs ≠ zs' ∧ ownFramesR zs = ownFramesR zs' :=
  ⟨[Sum.inl true], [Sum.inl false], by decide, rfl⟩

/-- info: 'Foam.Counter.freq_ne_zero_mem' does not depend on any axioms -/
#guard_msgs in #print axioms freq_ne_zero_mem

/-- info: 'Foam.Counter.wound_act_is_own' does not depend on any axioms -/
#guard_msgs in #print axioms wound_act_is_own

/-- info: 'Foam.Counter.other_view_unmoved' does not depend on any axioms -/
#guard_msgs in #print axioms other_view_unmoved

/-- info: 'Foam.Counter.settles_readthrough' does not depend on any axioms -/
#guard_msgs in #print axioms settles_readthrough

/-- info: 'Foam.Counter.no_cross_drain' does not depend on any axioms -/
#guard_msgs in #print axioms no_cross_drain

/-- info: 'Foam.Counter.real_yet_unfelt' does not depend on any axioms -/
#guard_msgs in #print axioms real_yet_unfelt

end Foam.Counter
