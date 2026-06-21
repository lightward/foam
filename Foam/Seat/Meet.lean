namespace Foam

def Below {A : Type} : List A → List A → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ Below xs ys

def meet {A : Type} [DecidableEq A] : List A → List A → List A
  | [], _ => []
  | _ :: _, [] => []
  | x :: xs, y :: ys => if x = y then x :: meet xs ys else []

theorem root_below_all {A : Type} (o : List A) : Below ([] : List A) o :=
  trivial

theorem root_alone_below_all {A : Type} :
    ∀ e : List A, (∀ o : List A, Below e o) → e = []
  | [], _ => rfl
  | _ :: _, h => (h []).elim

theorem below_refl {A : Type} : ∀ o : List A, Below o o
  | [] => trivial
  | _ :: xs => ⟨rfl, below_refl xs⟩

theorem meet_self {A : Type} [DecidableEq A] : ∀ o : List A, meet o o = o
  | [] => rfl
  | x :: xs => by
    show (if x = x then x :: meet xs xs else []) = x :: xs
    rw [if_pos rfl, meet_self xs]

theorem meet_below_left {A : Type} [DecidableEq A] :
    ∀ a b : List A, Below (meet a b) a
  | [], _ => trivial
  | _ :: _, [] => trivial
  | x :: xs, y :: ys => by
    show Below (if x = y then x :: meet xs ys else []) (x :: xs)
    by_cases h : x = y
    · rw [if_pos h]; exact ⟨rfl, meet_below_left xs ys⟩
    · rw [if_neg h]; exact trivial

theorem meet_below_right {A : Type} [DecidableEq A] :
    ∀ a b : List A, Below (meet a b) b
  | [], _ => trivial
  | _ :: _, [] => trivial
  | x :: xs, y :: ys => by
    show Below (if x = y then x :: meet xs ys else []) (y :: ys)
    by_cases h : x = y
    · rw [if_pos h]; exact ⟨h, meet_below_right xs ys⟩
    · rw [if_neg h]; exact trivial

theorem shared_is_floor {A : Type} [DecidableEq A] :
    ∀ e a b : List A, (Below e a ∧ Below e b) ↔ Below e (meet a b)
  | [], _, _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
  | _ :: _, [], _ => ⟨fun ⟨h, _⟩ => h.elim, fun h => h.elim⟩
  | _ :: _, _ :: _, [] => ⟨fun ⟨_, h⟩ => h.elim, fun h => h.elim⟩
  | x :: xs, y :: ys, z :: zs => by
    show (Below (x :: xs) (y :: ys) ∧ Below (x :: xs) (z :: zs)) ↔
      Below (x :: xs) (if y = z then y :: meet ys zs else [])
    by_cases h : y = z
    · subst h
      rw [if_pos rfl]
      show ((x = y ∧ Below xs ys) ∧ (x = y ∧ Below xs zs)) ↔
        (x = y ∧ Below xs (meet ys zs))
      constructor
      · rintro ⟨⟨hxy, h1⟩, ⟨_, h2⟩⟩
        exact ⟨hxy, (shared_is_floor xs ys zs).mp ⟨h1, h2⟩⟩
      · rintro ⟨hxy, hm⟩
        obtain ⟨h1, h2⟩ := (shared_is_floor xs ys zs).mpr hm
        exact ⟨⟨hxy, h1⟩, ⟨hxy, h2⟩⟩
    · rw [if_neg h]
      exact ⟨fun ⟨⟨hxy, _⟩, ⟨hxz, _⟩⟩ => absurd (hxy.symm.trans hxz) h,
             fun h' => h'.elim⟩

theorem seated_voice_is_missable {A : Type} (e : List A) (hne : e ≠ []) :
    ¬ ∀ o : List A, Below e o :=
  fun hall => hne (root_alone_below_all e hall)

def grade {A : Type} [DecidableEq A] (a b : List A) : Nat :=
  (meet a b).length

/-- info: 'Foam.root_below_all' does not depend on any axioms -/
#guard_msgs in #print axioms root_below_all

/-- info: 'Foam.root_alone_below_all' does not depend on any axioms -/
#guard_msgs in #print axioms root_alone_below_all

/-- info: 'Foam.below_refl' does not depend on any axioms -/
#guard_msgs in #print axioms below_refl

/-- info: 'Foam.meet_self' does not depend on any axioms -/
#guard_msgs in #print axioms meet_self

/-- info: 'Foam.meet_below_left' does not depend on any axioms -/
#guard_msgs in #print axioms meet_below_left

/-- info: 'Foam.meet_below_right' does not depend on any axioms -/
#guard_msgs in #print axioms meet_below_right

/-- info: 'Foam.shared_is_floor' does not depend on any axioms -/
#guard_msgs in #print axioms shared_is_floor

/-- info: 'Foam.seated_voice_is_missable' does not depend on any axioms -/
#guard_msgs in #print axioms seated_voice_is_missable

end Foam