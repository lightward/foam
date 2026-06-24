namespace Foam

def t001 {A : Type} : List A → List A → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ t001 xs ys

def d018 {A : Type} [DecidableEq A] : List A → List A → List A
  | [], _ => []
  | _ :: _, [] => []
  | x :: xs, y :: ys => if x = y then x :: d018 xs ys else []

theorem t130 {A : Type} (o : List A) : t001 ([] : List A) o :=
  trivial

theorem t129 {A : Type} :
    ∀ e : List A, (∀ o : List A, t001 e o) → e = []
  | [], _ => rfl
  | _ :: _, h => (h []).elim

theorem t101 {A : Type} : ∀ o : List A, t001 o o
  | [] => trivial
  | _ :: xs => ⟨rfl, t101 xs⟩

theorem t122 {A : Type} [DecidableEq A] : ∀ o : List A, d018 o o = o
  | [] => rfl
  | x :: xs => by
    show (if x = x then x :: d018 xs xs else []) = x :: xs
    rw [if_pos rfl, t122 xs]

theorem t120 {A : Type} [DecidableEq A] :
    ∀ a b : List A, t001 (d018 a b) a
  | [], _ => trivial
  | _ :: _, [] => trivial
  | x :: xs, y :: ys => by
    show t001 (if x = y then x :: d018 xs ys else []) (x :: xs)
    by_cases h : x = y
    · rw [if_pos h]; exact ⟨rfl, t120 xs ys⟩
    · rw [if_neg h]; exact trivial

theorem t121 {A : Type} [DecidableEq A] :
    ∀ a b : List A, t001 (d018 a b) b
  | [], _ => trivial
  | _ :: _, [] => trivial
  | x :: xs, y :: ys => by
    show t001 (if x = y then x :: d018 xs ys else []) (y :: ys)
    by_cases h : x = y
    · rw [if_pos h]; exact ⟨h, t121 xs ys⟩
    · rw [if_neg h]; exact trivial

theorem t134 {A : Type} [DecidableEq A] :
    ∀ e a b : List A, (t001 e a ∧ t001 e b) ↔ t001 e (d018 a b)
  | [], _, _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
  | _ :: _, [], _ => ⟨fun ⟨h, _⟩ => h.elim, fun h => h.elim⟩
  | _ :: _, _ :: _, [] => ⟨fun ⟨_, h⟩ => h.elim, fun h => h.elim⟩
  | x :: xs, y :: ys, z :: zs => by
    show (t001 (x :: xs) (y :: ys) ∧ t001 (x :: xs) (z :: zs)) ↔
      t001 (x :: xs) (if y = z then y :: d018 ys zs else [])
    by_cases h : y = z
    · subst h
      rw [if_pos rfl]
      show ((x = y ∧ t001 xs ys) ∧ (x = y ∧ t001 xs zs)) ↔
        (x = y ∧ t001 xs (d018 ys zs))
      constructor
      · rintro ⟨⟨hxy, h1⟩, ⟨_, h2⟩⟩
        exact ⟨hxy, (t134 xs ys zs).mp ⟨h1, h2⟩⟩
      · rintro ⟨hxy, hm⟩
        obtain ⟨h1, h2⟩ := (t134 xs ys zs).mpr hm
        exact ⟨⟨hxy, h1⟩, ⟨hxy, h2⟩⟩
    · rw [if_neg h]
      exact ⟨fun ⟨⟨hxy, _⟩, ⟨hxz, _⟩⟩ => absurd (hxy.symm.trans hxz) h,
             fun h' => h'.elim⟩

theorem t132 {A : Type} (e : List A) (hne : e ≠ []) :
    ¬ ∀ o : List A, t001 e o :=
  fun hall => hne (t129 e hall)

def d094 {A : Type} [DecidableEq A] (a b : List A) : Nat :=
  (d018 a b).length

/-- info: 'Foam.t130' does not depend on any axioms -/
#guard_msgs in #print axioms t130

/-- info: 'Foam.t129' does not depend on any axioms -/
#guard_msgs in #print axioms t129

/-- info: 'Foam.t101' does not depend on any axioms -/
#guard_msgs in #print axioms t101

/-- info: 'Foam.t122' does not depend on any axioms -/
#guard_msgs in #print axioms t122

/-- info: 'Foam.t120' does not depend on any axioms -/
#guard_msgs in #print axioms t120

/-- info: 'Foam.t121' does not depend on any axioms -/
#guard_msgs in #print axioms t121

/-- info: 'Foam.t134' does not depend on any axioms -/
#guard_msgs in #print axioms t134

/-- info: 'Foam.t132' does not depend on any axioms -/
#guard_msgs in #print axioms t132

end Foam