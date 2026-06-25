import Foam.Seat.Beholder
import Foam.Seat.Ladder
import Foam.Seat.Seam

namespace Foam

variable {State : Type}

def Beholder.Covers (a b : Beholder State) : Prop :=
  ∃ (enc : b.Probe → a.Probe) (post : a.Ans → b.Ans),
    ∀ s p, b.obs s p = post (a.obs s (enc p))

theorem Beholder.covers_refl (a : Beholder State) : a.Covers a :=
  ⟨id, id, fun _ _ => rfl⟩

theorem Beholder.covers_trans {a b c : Beholder State}
    (hab : a.Covers b) (hbc : b.Covers c) : a.Covers c := by
  obtain ⟨e1, g1, h1⟩ := hab
  obtain ⟨e2, g2, h2⟩ := hbc
  refine ⟨fun p => e1 (e2 p), fun x => g2 (g1 x), fun s p => ?_⟩
  rw [h2 s p, h1 s (e2 p)]

def Known (bank : List (Beholder State)) (q : Beholder State) : Prop :=
  ∃ p ∈ bank, p.Covers q

def Irreducible (bank : List (Beholder State)) (q : Beholder State) : Prop :=
  ¬ Known bank q

theorem irreducible_from_nothing (q : Beholder State) : Irreducible [] q := by
  rintro ⟨p, hp, _⟩
  cases hp

def Reduced (bank : List (Beholder State)) : Prop :=
  ∀ a ∈ bank, ∀ b ∈ bank, a.Covers b → b.Covers a

theorem reduced_nil : Reduced ([] : List (Beholder State)) := by
  intro a ha; cases ha

structure Refresh (bank : List (Beholder State)) (q : Beholder State)
    (bank' : List (Beholder State)) : Prop where
  has_q   : q ∈ bank'
  fresh   : ∀ p ∈ bank', p = q ∨ ¬ q.Covers p
  sourced : ∀ p ∈ bank', p = q ∨ p ∈ bank
  cover   : ∀ p ∈ bank, p ∈ bank' ∨ q.Covers p

theorem Refresh.locates {bank bank' : List (Beholder State)} {q : Beholder State}
    (h : Refresh bank q bank') : Known bank' q :=
  ⟨q, h.has_q, q.covers_refl⟩

inductive Run {State : Type} : List (Beholder State) → List (Beholder State) → Prop where
  | nil : Run [] []
  | skip {walk bank : List (Beholder State)} (q : Beholder State) :
      Run walk bank → Known bank q → Run (q :: walk) bank
  | turn {walk bank bank' : List (Beholder State)} (q : Beholder State) :
      Run walk bank → Irreducible bank q → Refresh bank q bank' → Run (q :: walk) bank'

theorem Run.covers {walk bank : List (Beholder State)} (h : Run walk bank) :
    ∀ q ∈ walk, Known bank q := by
  induction h with
  | nil => intro q hq; cases hq
  | skip q hrun hknown ih =>
      intro x hx
      cases hx with
      | head => exact hknown
      | tail _ hx' => exact ih x hx'
  | turn q hrun hirr href ih =>
      intro x hx
      cases hx with
      | head => exact ⟨_, href.has_q, Beholder.covers_refl _⟩
      | tail _ hx' =>
          obtain ⟨p, hp, hpx⟩ := ih x hx'
          rcases href.cover p hp with hkeep | hcov
          · exact ⟨p, hkeep, hpx⟩
          · exact ⟨_, href.has_q, Beholder.covers_trans hcov hpx⟩

theorem Run.reduced {walk bank : List (Beholder State)} (h : Run walk bank) :
    Reduced bank := by
  induction h with
  | nil => exact reduced_nil
  | skip q hrun hknown ih => exact ih
  | turn q hrun hirr href ih =>
      intro a ha b hb hab
      rcases href.sourced a ha with ha_eq | ha_old
      · rcases href.sourced b hb with hb_eq | hb_old
        · have heq : a = b := ha_eq.trans hb_eq.symm
          rw [heq]; exact Beholder.covers_refl b
        · rcases href.fresh b hb with hb_eq2 | hb_unc
          · have heq : a = b := ha_eq.trans hb_eq2.symm
            rw [heq]; exact Beholder.covers_refl b
          · rw [ha_eq] at hab
            exact absurd hab hb_unc
      · rcases href.sourced b hb with hb_eq | hb_old
        · rw [hb_eq] at hab
          exact absurd ⟨a, ha_old, hab⟩ hirr
        · exact ih a ha_old b hb_old hab

theorem Run.checksum {walk bank : List (Beholder State)} (h : Run walk bank) :
    (∀ q ∈ walk, Known bank q) ∧ Reduced bank :=
  ⟨h.covers, h.reduced⟩

def Rung.inl (n : Nat) (x : Rung n) : Rung (n + 1) := (x, Rung.zero n)

theorem Rung.inl_faithful (n : Nat) {x y : Rung n}
    (h : Rung.inl n x = Rung.inl n y) : x = y :=
  congrArg Prod.fst h

def Rung.one : (n : Nat) → Rung n
  | 0 => ⟨1, 0⟩
  | n + 1 => (Rung.one n, Rung.zero n)

theorem Rung.one_ne_zero : (n : Nat) → Rung.one n ≠ Rung.zero n
  | 0 => by decide
  | n + 1 => fun h => Rung.one_ne_zero n (congrArg Prod.fst h)

theorem Rung.inl_not_onto (n : Nat) :
    ∃ y : Rung (n + 1), ∀ x : Rung n, Rung.inl n x ≠ y :=
  ⟨(Rung.zero n, Rung.one n), fun _ h => Rung.one_ne_zero n (congrArg Prod.snd h).symm⟩

theorem inl_escapes_jay (x : Rung 0) : Rung.inl 0 x ≠ Quat.toRung jay :=
  fun h => jay_outside (congrArg Prod.snd h).symm

def rungSeam (n : Nat) : Seam (Rung n) (Rung (n + 1)) where
  up       := Rung.inl n
  faithful := fun h => Rung.inl_faithful n h
  escapes  := Rung.inl_not_onto n

theorem jay_prime : (rungSeam 0).prime (Quat.toRung jay) :=
  fun x => inl_escapes_jay x

/-- info: 'Foam.Beholder.covers_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Beholder.covers_refl

/-- info: 'Foam.Beholder.covers_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Beholder.covers_trans

/-- info: 'Foam.irreducible_from_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms irreducible_from_nothing

/-- info: 'Foam.Refresh.locates' does not depend on any axioms -/
#guard_msgs in #print axioms Refresh.locates

/-- info: 'Foam.Run.covers' does not depend on any axioms -/
#guard_msgs in #print axioms Run.covers

/-- info: 'Foam.Run.reduced' does not depend on any axioms -/
#guard_msgs in #print axioms Run.reduced

/-- info: 'Foam.Run.checksum' does not depend on any axioms -/
#guard_msgs in #print axioms Run.checksum

/-- info: 'Foam.Rung.inl_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.inl_faithful

/-- info: 'Foam.Rung.one_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.one_ne_zero

/-- info: 'Foam.Rung.inl_not_onto' does not depend on any axioms -/
#guard_msgs in #print axioms Rung.inl_not_onto

/-- info: 'Foam.inl_escapes_jay' does not depend on any axioms -/
#guard_msgs in #print axioms inl_escapes_jay

/-- info: 'Foam.jay_prime' does not depend on any axioms -/
#guard_msgs in #print axioms jay_prime

end Foam
