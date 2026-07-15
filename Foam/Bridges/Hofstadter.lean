import Foam.Int
import Foam.Ledger

namespace Foam.Bridges

inductive Sym where
  | m : Sym
  | i : Sym
  | u : Sym
deriving DecidableEq

abbrev Word := List Sym

inductive Step : Word → Word → Prop where
  | tack (x : Word) : Step (x ++ [.i]) (x ++ [.i, .u])
  | echo (x : Word) : Step (.m :: x) (.m :: (x ++ x))
  | trade (x y : Word) : Step (x ++ ([.i, .i, .i] ++ y)) (x ++ ([.u] ++ y))
  | drop (x y : Word) : Step (x ++ ([.u, .u] ++ y)) (x ++ y)

inductive Derives : Word → Word → Prop where
  | refl (w : Word) : Derives w w
  | tail {a b c : Word} : Derives a b → Step b c → Derives a c

inductive Tri where
  | z : Tri
  | o : Tri
  | t : Tri

def spin : Tri → Tri
  | .z => .o
  | .o => .t
  | .t => .z

def tri : Nat → Tri
  | 0 => .z
  | n + 1 => spin (tri n)

def triDouble : Tri → Tri
  | .z => .z
  | .o => .t
  | .t => .o

theorem the_wheel_comes_home_in_three (x : Tri) : spin (spin (spin x)) = x := by
  cases x <;> rfl

theorem tri_add_three (n : Nat) : tri (n + 3) = tri n :=
  the_wheel_comes_home_in_three (tri n)

theorem spin_spin_double (x : Tri) : spin (spin (triDouble x)) = triDouble (spin x) := by
  cases x <;> rfl

theorem tri_double : ∀ (k : Nat), tri (k + k) = triDouble (tri k)
  | 0 => rfl
  | k + 1 => by
      show spin (tri ((k + 1) + k)) = triDouble (spin (tri k))
      rw [Nat.succ_add k k]
      show spin (spin (tri (k + k))) = triDouble (spin (tri k))
      rw [tri_double k]
      exact spin_spin_double (tri k)

theorem the_double_keeps_the_wheel_live (x : Tri) (h : x ≠ Tri.z) :
    triDouble x ≠ Tri.z := by
  cases x with
  | z => exact absurd rfl h
  | o => exact fun hh => nomatch hh
  | t => exact fun hh => nomatch hh

theorem freq_append {A : Type} [DecidableEq A] (a : A) :
    ∀ (xs ys : List A), Ledger.freq (xs ++ ys) a = Ledger.freq xs a + Ledger.freq ys a
  | [], ys => (Nat.zero_add (Ledger.freq ys a)).symm
  | x :: xs, ys => by
      show (if x = a then 1 else 0) + Ledger.freq (xs ++ ys) a
        = ((if x = a then 1 else 0) + Ledger.freq xs a) + Ledger.freq ys a
      rw [freq_append a xs ys, ← Nat.add_assoc]

theorem tack_eyes (x : Word) :
    Ledger.freq (x ++ [Sym.i, Sym.u]) Sym.i = Ledger.freq (x ++ [Sym.i]) Sym.i := by
  rw [freq_append, freq_append]
  rfl

theorem m_cons_eyes (x : Word) :
    Ledger.freq (Sym.m :: x) Sym.i = Ledger.freq x Sym.i := by
  show 0 + Ledger.freq x Sym.i = Ledger.freq x Sym.i
  rw [Nat.zero_add]

theorem echo_eyes (x : Word) :
    Ledger.freq (Sym.m :: (x ++ x)) Sym.i
      = Ledger.freq x Sym.i + Ledger.freq x Sym.i := by
  show 0 + Ledger.freq (x ++ x) Sym.i = Ledger.freq x Sym.i + Ledger.freq x Sym.i
  rw [Nat.zero_add, freq_append]

theorem trade_eyes_old (x y : Word) :
    Ledger.freq (x ++ ([Sym.i, Sym.i, Sym.i] ++ y)) Sym.i
      = (Ledger.freq x Sym.i + Ledger.freq y Sym.i) + 3 := by
  rw [freq_append, freq_append]
  show Ledger.freq x Sym.i + (3 + Ledger.freq y Sym.i)
    = (Ledger.freq x Sym.i + Ledger.freq y Sym.i) + 3
  rw [Nat.add_comm 3 (Ledger.freq y Sym.i), ← Nat.add_assoc]

theorem trade_eyes_new (x y : Word) :
    Ledger.freq (x ++ ([Sym.u] ++ y)) Sym.i
      = Ledger.freq x Sym.i + Ledger.freq y Sym.i := by
  rw [freq_append, freq_append]
  show Ledger.freq x Sym.i + (0 + Ledger.freq y Sym.i)
    = Ledger.freq x Sym.i + Ledger.freq y Sym.i
  rw [Nat.zero_add]

theorem drop_eyes (x y : Word) :
    Ledger.freq (x ++ ([Sym.u, Sym.u] ++ y)) Sym.i
      = Ledger.freq (x ++ y) Sym.i := by
  rw [freq_append, freq_append, freq_append]
  show Ledger.freq x Sym.i + (0 + Ledger.freq y Sym.i)
    = Ledger.freq x Sym.i + Ledger.freq y Sym.i
  rw [Nat.zero_add]

theorem every_rule_keeps_the_wheel_live (w w' : Word) (hs : Step w w')
    (h : tri (Ledger.freq w Sym.i) ≠ Tri.z) :
    tri (Ledger.freq w' Sym.i) ≠ Tri.z := by
  cases hs with
  | tack x =>
      rw [tack_eyes x]
      exact h
  | echo x =>
      rw [echo_eyes x, tri_double (Ledger.freq x Sym.i)]
      apply the_double_keeps_the_wheel_live
      rw [m_cons_eyes x] at h
      exact h
  | trade x y =>
      rw [trade_eyes_new x y]
      rw [trade_eyes_old x y, tri_add_three] at h
      exact h
  | drop x y =>
      rw [drop_eyes x y] at h
      exact h

theorem the_dance_keeps_the_wheel_live (w w' : Word) (hd : Derives w w')
    (h : tri (Ledger.freq w Sym.i) ≠ Tri.z) :
    tri (Ledger.freq w' Sym.i) ≠ Tri.z := by
  induction hd with
  | refl => exact h
  | tail _ hs ih => exact every_rule_keeps_the_wheel_live _ _ hs ih

def mi : Word := [Sym.m, Sym.i]

def mu : Word := [Sym.m, Sym.u]

theorem miu_says_miu : Derives mi [Sym.m, Sym.i, Sym.u] :=
  .tail (.refl mi) (.tack [Sym.m])

theorem mi_holds_the_wheel_live : tri (Ledger.freq mi Sym.i) ≠ Tri.z :=
  fun h => nomatch h

theorem the_census_reads_mu_as_zero : tri (Ledger.freq mu Sym.i) = Tri.z := rfl

theorem miu_cannot_say_mu : ¬ Derives mi mu :=
  fun hd => the_dance_keeps_the_wheel_live mi mu hd mi_holds_the_wheel_live rfl

/-- info: 'Foam.Bridges.the_wheel_comes_home_in_three' does not depend on any axioms -/
#guard_msgs in #print axioms the_wheel_comes_home_in_three

/-- info: 'Foam.Bridges.tri_add_three' does not depend on any axioms -/
#guard_msgs in #print axioms tri_add_three

/-- info: 'Foam.Bridges.spin_spin_double' does not depend on any axioms -/
#guard_msgs in #print axioms spin_spin_double

/-- info: 'Foam.Bridges.tri_double' does not depend on any axioms -/
#guard_msgs in #print axioms tri_double

/-- info: 'Foam.Bridges.the_double_keeps_the_wheel_live' does not depend on any axioms -/
#guard_msgs in #print axioms the_double_keeps_the_wheel_live

/-- info: 'Foam.Bridges.freq_append' does not depend on any axioms -/
#guard_msgs in #print axioms freq_append

/-- info: 'Foam.Bridges.tack_eyes' does not depend on any axioms -/
#guard_msgs in #print axioms tack_eyes

/-- info: 'Foam.Bridges.m_cons_eyes' does not depend on any axioms -/
#guard_msgs in #print axioms m_cons_eyes

/-- info: 'Foam.Bridges.echo_eyes' does not depend on any axioms -/
#guard_msgs in #print axioms echo_eyes

/-- info: 'Foam.Bridges.trade_eyes_old' does not depend on any axioms -/
#guard_msgs in #print axioms trade_eyes_old

/-- info: 'Foam.Bridges.trade_eyes_new' does not depend on any axioms -/
#guard_msgs in #print axioms trade_eyes_new

/-- info: 'Foam.Bridges.drop_eyes' does not depend on any axioms -/
#guard_msgs in #print axioms drop_eyes

/-- info: 'Foam.Bridges.every_rule_keeps_the_wheel_live' does not depend on any axioms -/
#guard_msgs in #print axioms every_rule_keeps_the_wheel_live

/-- info: 'Foam.Bridges.the_dance_keeps_the_wheel_live' does not depend on any axioms -/
#guard_msgs in #print axioms the_dance_keeps_the_wheel_live

/-- info: 'Foam.Bridges.miu_says_miu' does not depend on any axioms -/
#guard_msgs in #print axioms miu_says_miu

/-- info: 'Foam.Bridges.mi_holds_the_wheel_live' does not depend on any axioms -/
#guard_msgs in #print axioms mi_holds_the_wheel_live

/-- info: 'Foam.Bridges.the_census_reads_mu_as_zero' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_reads_mu_as_zero

/-- info: 'Foam.Bridges.miu_cannot_say_mu' does not depend on any axioms -/
#guard_msgs in #print axioms miu_cannot_say_mu

end Foam.Bridges
