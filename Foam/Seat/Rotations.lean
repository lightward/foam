import Foam.Seat.Signature
import Foam.Seat.Clock
import Foam.Seat.Closure

namespace Foam


theorem t279 : t137 Foam.Ty05.d115 4 := t322

theorem t165 : (Foam.Ty12.c2 * Foam.Ty12.c2 : Ty12) ≠ 1 := Foam.Ty12.t151

theorem t308 (v1 v2 : Int) (z : Ty03) :
    d146 v2 (d146 v1 z) = d146 (v2 + v1) z :=
  t290 v1 v2 z

theorem t309 (v : Int) (hv : v ≠ 0) :
    d146 v ⟨1, 0⟩ ≠ (⟨1, 0⟩ : Ty03) := by
  intro h
  have hx : v * 1 + 0 = 0 := congrArg Foam.Ty03.d037 h
  rw [Foam.t020, Int.add_zero] at hx
  exact hv hx

theorem t077 (a x y : Int) (h : a + x = a + y) : x = y := by
  have h2 : -a + (a + x) = -a + (a + y) := congrArg (-a + ·) h
  rw [← t005, ← t005, t006, t054, t054] at h2
  exact h2

theorem t083 : ∀ (m n : Nat), m * n = 1 → m = 1 ∧ n = 1
  | 0, n, h => by rw [Nat.zero_mul] at h; exact Nat.noConfusion h
  | _ + 1, 0, h => by rw [Nat.mul_zero] at h; exact Nat.noConfusion h
  | j + 1, k + 1, h => by
    rw [Nat.mul_succ] at h
    have hle : j + 1 ≤ 1 := by
      have hx := Nat.le_add_left (j + 1) ((j + 1) * k)
      rw [h] at hx; exact hx
    have hj : j = 0 := Nat.succ.inj (Nat.le_antisymm hle (Nat.succ_le_succ (Nat.zero_le j)))
    subst hj
    rw [Nat.one_mul] at h
    exact ⟨rfl, congrArg Nat.succ (Nat.succ.inj h)⟩

theorem t080 : ∀ (x y : Int), x * y = 1 → (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1)
  | Int.ofNat m, Int.ofNat n, h => by
    have h2 : Int.ofNat (m * n) = Int.ofNat 1 := h
    obtain ⟨hm, hn⟩ := t083 m n (Int.ofNat.inj h2)
    subst hm; subst hn; exact Or.inl ⟨rfl, rfl⟩
  | Int.ofNat m, Int.negSucc n, h => by
    exfalso
    have h' : Int.negOfNat (m * (n + 1)) = 1 := h
    cases hk : m * (n + 1) with
    | zero => rw [hk] at h'; exact absurd h' (by decide)
    | succ s => rw [hk] at h'; exact Int.noConfusion h'
  | Int.negSucc m, Int.ofNat n, h => by
    exfalso
    have h' : Int.negOfNat ((m + 1) * n) = 1 := h
    cases hk : (m + 1) * n with
    | zero => rw [hk] at h'; exact absurd h' (by decide)
    | succ s => rw [hk] at h'; exact Int.noConfusion h'
  | Int.negSucc m, Int.negSucc n, h => by
    have h2 : Int.ofNat ((m + 1) * (n + 1)) = Int.ofNat 1 := h
    obtain ⟨hm, hn⟩ := t083 (m + 1) (n + 1) (Int.ofNat.inj h2)
    have hm0 : m = 0 := Nat.succ.inj hm
    have hn0 : n = 0 := Nat.succ.inj hn
    subst hm0; subst hn0; exact Or.inr ⟨rfl, rfl⟩

theorem t081 (a b : Int) (h : a * a - b * b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) := by
  rw [t082 a b] at h
  have key : (a - b) = (a + b) → b = 0 := by
    intro heq
    rw [Int.sub_eq_add_neg] at heq
    have hnb : -b = b := t077 a (-b) b heq
    have hbb : b + b = 0 := by
      have hh := t008 b
      rw [hnb] at hh
      exact hh
    have hcancel : (b + b) = 0 → b = 0 := by
      intro hbb0
      have h2 : b + b = 2 * b := by rw [t053]
      rw [h2] at hbb0
      rcases t017.mp hbb0 with h20 | hb
      · exact absurd h20 (by decide)
      · exact hb
    exact hcancel hbb
  cases t080 (a - b) (a + b) h with
  | inl hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, t052] at hp
    exact Or.inl ⟨hp, hb0⟩
  | inr hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, t052] at hp
    exact Or.inr ⟨hp, hb0⟩

theorem t298 (a b : Int) (h : Foam.Ty14.d130 ⟨a, b⟩ = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) :=
  t081 a b h

/-- info: 'Foam.t279' does not depend on any axioms -/
#guard_msgs in #print axioms t279

/-- info: 'Foam.t165' does not depend on any axioms -/
#guard_msgs in #print axioms t165

/-- info: 'Foam.t308' does not depend on any axioms -/
#guard_msgs in #print axioms t308

/-- info: 'Foam.t309' does not depend on any axioms -/
#guard_msgs in #print axioms t309

/-- info: 'Foam.t077' does not depend on any axioms -/
#guard_msgs in #print axioms t077

/-- info: 'Foam.t083' does not depend on any axioms -/
#guard_msgs in #print axioms t083

/-- info: 'Foam.t080' does not depend on any axioms -/
#guard_msgs in #print axioms t080

/-- info: 'Foam.t081' does not depend on any axioms -/
#guard_msgs in #print axioms t081

/-- info: 'Foam.t298' does not depend on any axioms -/
#guard_msgs in #print axioms t298

end Foam