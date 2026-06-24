import Foam.Scar
import Foam.Seat.Stage

namespace Foam

def t217 (S : Ty18) (m : S.Ty27 → S.Ty27) : Prop :=
  ∀ s p, S.d134 (m s) p = S.d134 s p

theorem t383 (S : Ty18) : t217 S (fun s => s) := fun _ _ => rfl

theorem t382 (S : Ty18) (m n : S.Ty27 → S.Ty27)
    (hm : t217 S m) (hn : t217 S n) : t217 S (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

def d153 (S : Ty18) (s : S.Ty27) : List S.Ty26 → List S.Ty25
  | [] => []
  | p :: ps => S.d134 s p :: d153 S s ps

def d154 (S : Ty18) (m : S.Ty27 → S.Ty27) :
    S.Ty27 → List S.Ty26 → List S.Ty25
  | _, [] => []
  | s, p :: ps => S.d134 (m s) p :: d154 S m (m s) ps

theorem t327 (S : Ty18) (ps : List S.Ty26) :
    ∀ {t s : S.Ty27}, (∀ p, S.d134 t p = S.d134 s p) →
      d153 S t ps = d153 S s ps := by
  induction ps with
  | nil => intro t s _; rfl
  | cons p ps ih =>
    intro t s h
    show S.d134 t p :: d153 S t ps = S.d134 s p :: d153 S s ps
    rw [h p, ih h]

theorem t386 (S : Ty18) (m : S.Ty27 → S.Ty27)
    (h : t217 S m) (ps : List S.Ty26) :
    ∀ s, d154 S m s ps = d153 S s ps := by
  induction ps with
  | nil => intro s; rfl
  | cons p ps ih =>
    intro s
    show S.d134 (m s) p :: d154 S m (m s) ps = S.d134 s p :: d153 S s ps
    rw [h s p, ih (m s), t327 S ps (h s)]

def d022 : Int → Nat
  | Int.ofNat m => m
  | Int.negSucc _ => 0

theorem t320 : ∀ b : Int, d022 (d141 b b) = d022 b
  | Int.ofNat _ => rfl
  | Int.negSucc 0 => rfl
  | Int.negSucc (_ + 1) => rfl

theorem t164 : ∃ b : Int, d022 (d086 b b) ≠ d022 b :=
  ⟨1, fun h => Nat.noConfusion h⟩

def d029 : Ty18 := ⟨Int, Unit, Nat, fun b _ => d022 b⟩

theorem t400 : t217 d029 (fun b => d141 b b) :=
  fun b _ => t320 b

/-- info: 'Foam.t382' does not depend on any axioms -/
#guard_msgs in #print axioms t382

/-- info: 'Foam.t327' does not depend on any axioms -/
#guard_msgs in #print axioms t327

/-- info: 'Foam.t386' does not depend on any axioms -/
#guard_msgs in #print axioms t386

/-- info: 'Foam.t320' does not depend on any axioms -/
#guard_msgs in #print axioms t320

/-- info: 'Foam.t164' does not depend on any axioms -/
#guard_msgs in #print axioms t164

/-- info: 'Foam.t400' does not depend on any axioms -/
#guard_msgs in #print axioms t400

end Foam
