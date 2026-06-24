import Foam.Seat.Beholder
import Foam.Seat.Ladder
import Foam.Seat.Seam

namespace Foam

variable {State : Type}

def Ty01.t198 (a b : Ty01 State) : Prop :=
  ∃ (enc : b.Ty20 → a.Ty20) (post : a.Ty19 → b.Ty19),
    ∀ s p, b.d102 s p = post (a.d102 s (enc p))

theorem Ty01.t332 (a : Ty01 State) : a.t198 a :=
  ⟨id, id, fun _ _ => rfl⟩

theorem Ty01.t333 {a b c : Ty01 State}
    (hab : a.t198 b) (hbc : b.t198 c) : a.t198 c := by
  obtain ⟨e1, g1, h1⟩ := hab
  obtain ⟨e2, g2, h2⟩ := hbc
  refine ⟨fun p => e1 (e2 p), fun x => g2 (g1 x), fun s p => ?_⟩
  rw [h2 s p, h1 s (e2 p)]

def t354 (bank : List (Ty01 State)) (q : Ty01 State) : Prop :=
  ∃ p ∈ bank, p.t198 q

def t426 (bank : List (Ty01 State)) (q : Ty01 State) : Prop :=
  ¬ t354 bank q

theorem t488 (q : Ty01 State) : t426 [] q := by
  rintro ⟨p, hp, _⟩
  cases hp

def t356 (bank : List (Ty01 State)) : Prop :=
  ∀ a ∈ bank, ∀ b ∈ bank, a.t198 b → b.t198 a

theorem t473 : t356 ([] : List (Ty01 State)) := by
  intro a ha; cases ha

structure t099 (bank : List (Ty01 State)) (q : Ty01 State)
    (bank' : List (Ty01 State)) : Prop where
  t148   : q ∈ bank'
  t358   : ∀ p ∈ bank', p = q ∨ ¬ q.t198 p
  t149 : ∀ p ∈ bank', p = q ∨ p ∈ bank
  t357   : ∀ p ∈ bank, p ∈ bank' ∨ q.t198 p

theorem t099.t427 {bank bank' : List (Ty01 State)} {q : Ty01 State}
    (h : t099 bank q bank') : t354 bank' q :=
  ⟨q, h.t148, q.t332⟩

inductive t100 {State : Type} : List (Ty01 State) → List (Ty01 State) → Prop where
  | c7 : t100 [] []
  | c8 {walk bank : List (Ty01 State)} (q : Ty01 State) :
      t100 walk bank → t354 bank q → t100 (q :: walk) bank
  | c9 {walk bank bank' : List (Ty01 State)} (q : Ty01 State) :
      t100 walk bank → t426 bank q → t099 bank q bank' → t100 (q :: walk) bank'

theorem t100.t432 {walk bank : List (Ty01 State)} (h : t100 walk bank) :
    ∀ q ∈ walk, t354 bank q := by
  induction h with
  | c7 => intro q hq; cases hq
  | c8 q hrun hknown ih =>
      intro x hx
      cases hx with
      | head => exact hknown
      | tail _ hx' => exact ih x hx'
  | c9 q hrun hirr href ih =>
      intro x hx
      cases hx with
      | head => exact ⟨_, href.t148, Foam.Ty01.t332 _⟩
      | tail _ hx' =>
          obtain ⟨p, hp, hpx⟩ := ih x hx'
          rcases href.t357 p hp with hkeep | hcov
          · exact ⟨p, hkeep, hpx⟩
          · exact ⟨_, href.t148, Foam.Ty01.t333 hcov hpx⟩

theorem t100.t433 {walk bank : List (Ty01 State)} (h : t100 walk bank) :
    t356 bank := by
  induction h with
  | c7 => exact t473
  | c8 q hrun hknown ih => exact ih
  | c9 q hrun hirr href ih =>
      intro a ha b hb hab
      rcases href.t149 a ha with ha_eq | ha_old
      · rcases href.t149 b hb with hb_eq | hb_old
        · have heq : a = b := ha_eq.trans hb_eq.symm
          rw [heq]; exact Foam.Ty01.t332 b
        · rcases href.t358 b hb with hb_eq2 | hb_unc
          · have heq : a = b := ha_eq.trans hb_eq2.symm
            rw [heq]; exact Foam.Ty01.t332 b
          · rw [ha_eq] at hab
            exact absurd hab hb_unc
      · rcases href.t149 b hb with hb_eq | hb_old
        · rw [hb_eq] at hab
          exact absurd ⟨a, ha_old, hab⟩ hirr
        · exact ih a ha_old b hb_old hab

theorem t100.t431 {walk bank : List (Ty01 State)} (h : t100 walk bank) :
    (∀ q ∈ walk, t354 bank q) ∧ t356 bank :=
  ⟨h.t432, h.t433⟩

def Ty13.d127 (n : Nat) (x : Ty13 n) : Ty13 (n + 1) := (x, Foam.Ty13.d074 n)

theorem Ty13.t233 (n : Nat) {x y : Ty13 n}
    (h : Foam.Ty13.d127 n x = Foam.Ty13.d127 n y) : x = y :=
  congrArg Prod.fst h

def Ty13.d072 : (n : Nat) → Ty13 n
  | 0 => ⟨1, 0⟩
  | n + 1 => (Foam.Ty13.d072 n, Foam.Ty13.d074 n)

theorem Ty13.t156 : (n : Nat) → Foam.Ty13.d072 n ≠ Foam.Ty13.d074 n
  | 0 => by decide
  | n + 1 => fun h => Foam.Ty13.t156 n (congrArg Prod.fst h)

theorem Ty13.t234 (n : Nat) :
    ∃ y : Ty13 (n + 1), ∀ x : Ty13 n, Foam.Ty13.d127 n x ≠ y :=
  ⟨(Foam.Ty13.d074 n, Foam.Ty13.d072 n), fun _ h => Foam.Ty13.t156 n (congrArg Prod.snd h).symm⟩

theorem t301 (x : Ty13 0) : Foam.Ty13.d127 0 x ≠ Foam.Ty10.d122 d097 :=
  fun h => t178 (congrArg Prod.snd h).symm

def d225 (n : Nat) : Ty15 (Ty13 n) (Ty13 (n + 1)) where
  d079       := Foam.Ty13.d127 n
  t158 := fun h => Foam.Ty13.t233 n h
  t157  := Foam.Ty13.t234 n

theorem t462 : (d225 0).t160 (Foam.Ty10.d122 d097) :=
  fun x => t301 x

/-- info: 'Foam.Ty01.t332' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty01.t332

/-- info: 'Foam.Ty01.t333' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty01.t333

/-- info: 'Foam.t488' does not depend on any axioms -/
#guard_msgs in #print axioms t488

/-- info: 'Foam.t099.t427' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t099.t427

/-- info: 'Foam.t100.t432' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t100.t432

/-- info: 'Foam.t100.t433' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t100.t433

/-- info: 'Foam.t100.t431' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t100.t431

/-- info: 'Foam.Ty13.t233' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t233

/-- info: 'Foam.Ty13.t156' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t156

/-- info: 'Foam.Ty13.t234' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t234

/-- info: 'Foam.t301' does not depend on any axioms -/
#guard_msgs in #print axioms t301

/-- info: 'Foam.t462' does not depend on any axioms -/
#guard_msgs in #print axioms t462

end Foam
