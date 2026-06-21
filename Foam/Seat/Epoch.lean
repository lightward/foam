import Foam.Seat.Beholder

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

def Irredundant : List (Beholder State) → Prop
  | [] => True
  | q :: rest => Irreducible rest q ∧ Irredundant rest

theorem irreducible_from_nothing (q : Beholder State) : Irreducible [] q := by
  rintro ⟨p, hp, _⟩
  cases hp

def epoch (bank : List (Beholder State)) (q : Beholder State)
    (_ : Irreducible bank q) : List (Beholder State) := q :: bank

theorem epoch_turns_over (bank : List (Beholder State)) (q : Beholder State)
    (h : Irreducible bank q) :
    Known (epoch bank q h) q ∧ (Irredundant bank → Irredundant (epoch bank q h)) := by
  show Known (q :: bank) q ∧ (Irredundant bank → Irredundant (q :: bank))
  exact ⟨⟨q, List.Mem.head bank, q.covers_refl⟩, fun hb => ⟨h, hb⟩⟩

inductive Run {State : Type} : List (Beholder State) → List (Beholder State) → Prop where
  | nil : Run [] []
  | skip {walk bank : List (Beholder State)} (q : Beholder State) :
      Run walk bank → Known bank q → Run (q :: walk) bank
  | turn {walk bank : List (Beholder State)} (q : Beholder State) :
      Run walk bank → Irreducible bank q → Run (q :: walk) (q :: bank)

theorem Run.covers {walk bank : List (Beholder State)} (h : Run walk bank) :
    ∀ q ∈ walk, Known bank q := by
  induction h with
  | nil => intro q hq; cases hq
  | skip q hrun hknown ih =>
      intro x hx
      cases hx with
      | head => exact hknown
      | tail _ hx' => exact ih x hx'
  | turn q hrun hirr ih =>
      intro x hx
      cases hx with
      | head => exact ⟨_, List.Mem.head _, Beholder.covers_refl _⟩
      | tail _ hx' =>
          obtain ⟨p, hp, hpx⟩ := ih x hx'
          exact ⟨p, List.Mem.tail _ hp, hpx⟩

theorem Run.irredundant {walk bank : List (Beholder State)} (h : Run walk bank) :
    Irredundant bank := by
  induction h with
  | nil => trivial
  | skip q hrun hknown ih => exact ih
  | turn q hrun hirr ih => exact ⟨hirr, ih⟩

theorem Run.kolmogorov {walk bank : List (Beholder State)} (h : Run walk bank) :
    (∀ q ∈ walk, Known bank q) ∧ Irredundant bank :=
  ⟨h.covers, h.irredundant⟩

/-- info: 'Foam.Beholder.covers_refl' does not depend on any axioms -/
#guard_msgs in #print axioms Beholder.covers_refl

/-- info: 'Foam.Beholder.covers_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Beholder.covers_trans

/-- info: 'Foam.irreducible_from_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms irreducible_from_nothing

/-- info: 'Foam.epoch_turns_over' does not depend on any axioms -/
#guard_msgs in #print axioms epoch_turns_over

/-- info: 'Foam.Run.covers' does not depend on any axioms -/
#guard_msgs in #print axioms Run.covers

/-- info: 'Foam.Run.irredundant' does not depend on any axioms -/
#guard_msgs in #print axioms Run.irredundant

/-- info: 'Foam.Run.kolmogorov' does not depend on any axioms -/
#guard_msgs in #print axioms Run.kolmogorov

end Foam
