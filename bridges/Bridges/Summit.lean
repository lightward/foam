import Foam.Seat.Summit

/-!
# Summit — the seat of a bounded ascent is classical

The axiom-free side (`Foam/Seat/Summit.lean`) carries everything an
arriving chain can verify on its own: a strict climb escapes every bound
(`climbs_escape` — the `hollowChain` shadow at Nat scale), a bounded
ascent must rest (`bounded_rests` — the witness found by decidable search
inside the bound), and a seat is exactly rest-forever
(`seated_iff_rests_forever`).  A closed orbit needs none of this: one lap
carries the whole future (`lap_carries`), constructively.

What the axiom-free side cannot do — provably cannot, by the usual
halting encoding (`c n := 1` once the machine has halted) — is *locate
the seat* of a bounded ascent: eventually-constant-from-here is a Π⁰₁
fact per candidate index, and no bounded search decides it.  Here, with
`Classical.byContradiction`, the seat exists (`bounded_ascent_seated`).
The receipt stamps the observer: `[propext, Classical.choice, Quot.sound]`
— the same triple the FTPG deaxiomatization pays per atom — enters exactly
at the summit and nowhere below it (every lemma underneath is axiom-free).

This is the FTPG hole at counter scale.  `Hollow.lean` shows the
infinite chain whose seat is missing (completeness refused); this file
shows that even where the seat cannot be missing, pointing at it is
conjured, not computed.  Completeness is closure someone must sit in:
the observer is byo.
-/

namespace Foam.Bridges

theorem exists_larger {c : Nat → Nat} (hc : Ascends c) {n : Nat}
    (h : ¬ Seated c n) : ∃ m, n ≤ m ∧ c n < c m :=
  Classical.byContradiction fun hno =>
    h fun m hm =>
      have hnlt : ¬ (c n < c m) := fun hlt => hno ⟨m, hm, hlt⟩
      Nat.le_antisymm (Nat.le_of_not_lt hnlt) (ascends_le hc hm)

theorem unseated_grows {c : Nat → Nat} (hc : Ascends c)
    (h : ∀ n, ¬ Seated c n) : ∀ k, ∃ n, c 0 + k ≤ c n := by
  intro k
  induction k with
  | zero => exact ⟨0, Nat.le_refl _⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, _, hlt⟩ := exists_larger hc (h n)
      exact ⟨m, Nat.le_trans (Nat.succ_le_succ hn) (Nat.succ_le_of_lt hlt)⟩

theorem bounded_ascent_seated {c : Nat → Nat} (hc : Ascends c) (B : Nat)
    (hB : ∀ n, c n ≤ B) : ∃ n, Seated c n :=
  Classical.byContradiction fun h =>
    have h' : ∀ n, ¬ Seated c n := fun n hn => h ⟨n, hn⟩
    match unseated_grows hc h' (B + 1) with
    | ⟨n, hn⟩ =>
        Nat.not_succ_le_self B
          (Nat.le_trans (Nat.le_trans (Nat.le_add_left (B + 1) (c 0)) hn) (hB n))

/-- info: 'Foam.Bridges.bounded_ascent_seated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bounded_ascent_seated

end Foam.Bridges
