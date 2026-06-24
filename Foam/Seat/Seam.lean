import Foam.Seat

namespace Foam

structure Ty15 (A B : Type) where
  d079       : A → B
  t158 : ∀ {x y : A}, d079 x = d079 y → x = y
  t157  : ∃ y : B, ∀ x : A, d079 x ≠ y

def Ty15.t160 {A B : Type} (S : Ty15 A B) (q : B) : Prop := ∀ x : A, S.d079 x ≠ q

theorem Ty15.t159 {A B : Type} (S : Ty15 A B) :
    ¬ ∃ g : B → A, ∀ b, S.d079 (g b) = b := by
  rintro ⟨g, hg⟩
  obtain ⟨y, hy⟩ := S.t157
  exact hy (g y) (hg y)

def d020 {S : Type} : List S → Nat → Option S
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: l, n + 1 => d020 l n

theorem t124 {S : Type} : ∀ s t : List S, (∀ n, d020 s n = d020 t n) → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h 0
  | _ :: _, [], h => nomatch h 0
  | a :: s, b :: t, h => by
    injection h 0 with hab
    rw [hab, t124 s t (fun n => h (n + 1))]

theorem t126 {S : Type} : ∀ (l : List S) (n : Nat), d020 l n = none → d020 l (n + 1) = none
  | [], _, _ => rfl
  | _ :: _, 0, h => nomatch h
  | _ :: l, n + 1, h => t126 l n h

theorem t125 {S : Type} : ∀ l : List S, d020 l l.length = none
  | [] => rfl
  | _ :: l => t125 l

structure Ty02 (S : Type) where
  d033    : Nat → Option S
  t138 : ∀ n, d033 n = none → d033 (n + 1) = none

def d152 {S : Type} (l : List S) : Ty02 S := ⟨d020 l, t126 l⟩

def d093 {S : Type} (s : S) : Ty02 S := ⟨fun _ => some s, fun _ h => nomatch h⟩

theorem t285 {S : Type} (s : S) (l : List S) :
    ∃ n, (d152 l).d033 n ≠ (d093 s).d033 n :=
  ⟨l.length, fun h => nomatch (t125 l).symm.trans h⟩

theorem t311 {S : Type} (l l' : List S)
    (h : ∀ n, (d152 l).d033 n = (d152 l').d033 n) : l = l' :=
  t124 l l' h

def d193 {S : Type} (s : S) : Ty15 (List S) (Ty02 S) where
  d079       := d152
  t158 := fun {l l'} h => t311 l l' (fun n => congrArg (fun c => c.d033 n) h)
  t157  := ⟨d093 s, fun l h => (t285 s l).elim (fun n hn => hn (congrArg (fun c => c.d033 n) h))⟩

theorem t312 {S : Type} (s : S) :
    ¬ ∃ g : Ty02 S → List S, ∀ c, d152 (g c) = c :=
  Foam.Ty15.t159 (d193 s)

theorem t319 {S : Type} (s : S) :
    (∀ l l' : List S, (∀ n, (d152 l).d033 n = (d152 l').d033 n) → l = l')
      ∧ ¬ ∃ g : Ty02 S → List S, ∀ c, d152 (g c) = c :=
  ⟨t311, t312 s⟩

/-- info: 'Foam.Ty15.t159' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty15.t159

/-- info: 'Foam.d193' does not depend on any axioms -/
#guard_msgs in #print axioms d193

/-- info: 'Foam.t311' does not depend on any axioms -/
#guard_msgs in #print axioms t311

/-- info: 'Foam.t312' does not depend on any axioms -/
#guard_msgs in #print axioms t312

/-- info: 'Foam.t319' does not depend on any axioms -/
#guard_msgs in #print axioms t319

end Foam
