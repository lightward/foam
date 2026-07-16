import Foam.Int
import Foam.Ledger
import Foam.Golden
import Foam.Bridges.Zeckendorf
import Foam.Bridges.Narayana
import Foam.Bridges.Leibniz
import Foam.Bridges.Fraenkel
import Foam.Bridges.Poncelet

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

def fibN : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibN (n + 1) + fibN n

theorem fibN_gnomon (n : Nat) : fibN (n + 2) = fibN (n + 1) + fibN n := rfl

def worth : Nat → List Bool → Nat
  | _, [] => 0
  | i, false :: ds => worth (i + 1) ds
  | i, true :: ds => fibN i + worth (i + 1) ds

theorem worth_gnomon : ∀ (ds : List Bool) (i : Nat),
    worth (i + 2) ds = worth (i + 1) ds + worth i ds
  | [], _ => rfl
  | false :: rest, i => worth_gnomon rest (i + 1)
  | true :: rest, i => by
      show fibN (i + 2) + worth ((i + 1) + 2) rest
        = (fibN (i + 1) + worth ((i + 1) + 1) rest) + (fibN i + worth (i + 1) rest)
      rw [worth_gnomon rest (i + 1), fibN_gnomon]
      exact add_shuffle (fibN (i + 1)) (fibN i)
        (worth ((i + 1) + 1) rest) (worth (i + 1) rest)

def lit : List Bool → Bool
  | [] => false
  | d :: _ => d

theorem noconsec_tail : ∀ {d : Bool} {ds : List Bool}, NoConsec (d :: ds) → NoConsec ds
  | _, [], _ => True.intro
  | false, _ :: _, h => h
  | true, false :: _, h => h
  | true, true :: _, h => h.elim

theorem noconsec_head : ∀ {ds : List Bool}, NoConsec (true :: ds) → lit ds = false
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: _, h => h.elim

theorem noconsec_false_cons : ∀ {ds : List Bool}, NoConsec ds → NoConsec (false :: ds)
  | [], _ => True.intro
  | _ :: _, h => h

def carry : List Bool → List Bool
  | [] => [true]
  | [_] => [true]
  | _ :: false :: rest => true :: false :: rest
  | _ :: true :: rest => false :: false :: carry rest

theorem carry_pays : ∀ (ds : List Bool) (i : Nat), NoConsec ds → lit ds = false →
    worth i (carry ds) = fibN i + worth i ds
  | [], _, _, _ => rfl
  | [false], _, _, _ => rfl
  | [true], _, _, hd => nomatch hd
  | true :: _ :: _, _, _, hd => nomatch hd
  | false :: false :: _, _, _, _ => rfl
  | false :: true :: rest, i, hnc, _ => by
      show worth (i + 2) (carry rest) = fibN i + (fibN (i + 1) + worth (i + 2) rest)
      rw [carry_pays rest (i + 2) (noconsec_tail (noconsec_tail hnc))
            (noconsec_head (noconsec_tail hnc)),
          ← Nat.add_assoc (fibN i) (fibN (i + 1)) (worth (i + 2) rest),
          Nat.add_comm (fibN i) (fibN (i + 1)), ← fibN_gnomon]

theorem carry_spaces : ∀ (ds : List Bool), NoConsec ds → lit ds = false →
    NoConsec (carry ds)
  | [], _, _ => True.intro
  | [false], _, _ => True.intro
  | [true], _, hd => nomatch hd
  | true :: _ :: _, _, hd => nomatch hd
  | false :: false :: _, h, _ => h
  | false :: true :: rest, h, _ =>
      noconsec_false_cons (noconsec_false_cons
        (carry_spaces rest (noconsec_tail (noconsec_tail h))
          (noconsec_head (noconsec_tail h))))

def click : List Bool → List Bool
  | [] => [true]
  | false :: rest => carry (false :: rest)
  | true :: rest => false :: carry rest

theorem click_counts : ∀ (ds : List Bool), NoConsec ds →
    worth 2 (click ds) = worth 2 ds + 1
  | [], _ => rfl
  | false :: rest, h => by
      show worth 2 (carry (false :: rest)) = worth 2 (false :: rest) + 1
      rw [carry_pays (false :: rest) 2 h rfl]
      exact Nat.add_comm 1 (worth 2 (false :: rest))
  | true :: rest, h => by
      show worth 3 (carry rest) = (fibN 2 + worth 3 rest) + 1
      rw [carry_pays rest 3 (noconsec_tail h) (noconsec_head h)]
      show 2 + worth 3 rest = (1 + worth 3 rest) + 1
      rw [Nat.add_comm 1 (worth 3 rest)]
      exact Nat.add_comm 2 (worth 3 rest)

theorem click_spaces : ∀ (ds : List Bool), NoConsec ds → NoConsec (click ds)
  | [], _ => True.intro
  | false :: rest, h => carry_spaces (false :: rest) h rfl
  | true :: rest, h =>
      noconsec_false_cons (carry_spaces rest (noconsec_tail h) (noconsec_head h))

theorem click_holds_the_shadow : ∀ (ds : List Bool), NoConsec ds → lit ds = true →
    worth 1 (click ds) = worth 1 ds
  | [], _, hl => nomatch hl
  | false :: _, _, hl => nomatch hl
  | true :: rest, h, _ => by
      show worth 2 (carry rest) = fibN 1 + worth 2 rest
      rw [carry_pays rest 2 (noconsec_tail h) (noconsec_head h)]
      rfl

theorem click_moves_the_shadow : ∀ (ds : List Bool), NoConsec ds → lit ds = false →
    worth 1 (click ds) = worth 1 ds + 1
  | [], _, _ => rfl
  | false :: rest, h, _ => by
      show worth 1 (carry (false :: rest)) = worth 1 (false :: rest) + 1
      rw [carry_pays (false :: rest) 1 h rfl]
      exact Nat.add_comm 1 (worth 1 (false :: rest))
  | true :: _, _, hl => nomatch hl

theorem a_lit_lamp_casts_a_shadow : ∀ (ds : List Bool), lit ds = true → 1 ≤ worth 1 ds
  | true :: rest, _ => Nat.le_add_right 1 (worth 2 rest)
  | [], hl => nomatch hl
  | false :: _, hl => nomatch hl

def odometer : Nat → List Bool
  | 0 => []
  | n + 1 => click (odometer n)

theorem the_odometer_spaces : ∀ (n : Nat), NoConsec (odometer n)
  | 0 => True.intro
  | n + 1 => click_spaces (odometer n) (the_odometer_spaces n)

theorem the_odometer_reads_true : ∀ (n : Nat), worth 2 (odometer n) = n
  | 0 => rfl
  | n + 1 => by
      show worth 2 (click (odometer n)) = n + 1
      rw [click_counts (odometer n) (the_odometer_spaces n), the_odometer_reads_true n]

def G (n : Nat) : Nat := worth 1 (odometer n)

theorem g_hums_its_opening_bars :
    (G 0, G 1, G 2, G 3, G 4, G 5, G 6, G 7) = (0, 1, 1, 2, 3, 3, 4, 4) := rfl

def downshift : List Bool → List Bool
  | [] => []
  | false :: rest => rest
  | true :: rest => carry rest

theorem the_downshift_reads_the_shadow : ∀ (ds : List Bool), NoConsec ds →
    worth 2 (downshift ds) = worth 1 ds
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: rest, h => by
      show worth 2 (carry rest) = fibN 1 + worth 2 rest
      rw [carry_pays rest 2 (noconsec_tail h) (noconsec_head h)]
      rfl

theorem the_downshift_spaces : ∀ (ds : List Bool), NoConsec ds →
    NoConsec (downshift ds)
  | [], _ => True.intro
  | false :: _, h => noconsec_tail h
  | true :: rest, h => carry_spaces rest (noconsec_tail h) (noconsec_head h)

theorem the_double_shadow : ∀ (ds : List Bool), NoConsec ds →
    worth 1 (downshift ds) = worth 0 ds + cond (lit ds) 1 0
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: rest, h => by
      show worth 1 (carry rest) = (fibN 0 + worth 1 rest) + 1
      rw [carry_pays rest 1 (noconsec_tail h) (noconsec_head h)]
      show 1 + worth 1 rest = (0 + worth 1 rest) + 1
      rw [Nat.zero_add]
      exact Nat.add_comm 1 (worth 1 rest)

theorem downshift_click_lit : ∀ (ds : List Bool), lit ds = true →
    downshift (click ds) = downshift ds
  | [], hl => nomatch hl
  | false :: _, hl => nomatch hl
  | true :: _, _ => rfl

theorem downshift_click_unlit : ∀ (ds : List Bool), lit ds = false →
    downshift (click ds) = click (downshift ds)
  | [], _ => rfl
  | [false], _ => rfl
  | false :: false :: _, _ => rfl
  | false :: true :: _, _ => rfl
  | true :: _, hl => nomatch hl

theorem the_shadow_walks_the_downshift : ∀ (n : Nat),
    odometer (G n) = downshift (odometer n)
  | 0 => rfl
  | n + 1 => by
      cases hl : lit (odometer n) with
      | true =>
          show odometer (worth 1 (click (odometer n))) = downshift (click (odometer n))
          rw [click_holds_the_shadow (odometer n) (the_odometer_spaces n) hl,
              downshift_click_lit (odometer n) hl]
          exact the_shadow_walks_the_downshift n
      | false =>
          show odometer (worth 1 (click (odometer n))) = downshift (click (odometer n))
          rw [click_moves_the_shadow (odometer n) (the_odometer_spaces n) hl,
              downshift_click_unlit (odometer n) hl]
          exact congrArg click (the_shadow_walks_the_downshift n)

theorem the_walker_carries_its_shadow (n : Nat) : G n + worth 0 (odometer n) = n :=
  ((the_odometer_reads_true n).symm.trans (worth_gnomon (odometer n) 0)).symm

theorem the_shadow_never_outruns_the_walker (n : Nat) : G n ≤ n :=
  Nat.le.intro (the_walker_carries_its_shadow n)

theorem the_two_shadows_balance (n : Nat) :
    G n + G (G n) = n + cond (lit (odometer n)) 1 0 := by
  show G n + worth 1 (odometer (G n)) = n + cond (lit (odometer n)) 1 0
  rw [the_shadow_walks_the_downshift n,
      the_double_shadow (odometer n) (the_odometer_spaces n),
      ← Nat.add_assoc (G n) (worth 0 (odometer n)) (cond (lit (odometer n)) 1 0),
      the_walker_carries_its_shadow n]

theorem the_loop_closes (n : Nat) : G (n + 1) + G (G n) = n + 1 := by
  cases hl : lit (odometer n) with
  | true =>
      have hstep : G (n + 1) = G n :=
        click_holds_the_shadow (odometer n) (the_odometer_spaces n) hl
      have hbal := the_two_shadows_balance n
      rw [hl] at hbal
      rw [hstep]
      exact hbal
  | false =>
      have hstep : G (n + 1) = G n + 1 :=
        click_moves_the_shadow (odometer n) (the_odometer_spaces n) hl
      have hbal := the_two_shadows_balance n
      rw [hl] at hbal
      rw [hstep, Nat.add_comm (G n) 1, Nat.add_assoc]
      show 1 + (G n + G (G n)) = n + 1
      rw [hbal]
      exact Nat.add_comm 1 n

theorem sub_both_tick : ∀ (a b : Nat), (a + 1) - (b + 1) = a - b
  | _, 0 => rfl
  | a, b + 1 => congrArg Nat.pred (sub_both_tick a b)

theorem add_then_sub : ∀ (a b : Nat), (a + b) - b = a
  | _, 0 => rfl
  | a, b + 1 => (sub_both_tick (a + b) b).trans (add_then_sub a b)

theorem the_grounded_object_satisfies_the_loop (n : Nat) :
    G (n + 1) = (n + 1) - G (G n) :=
  calc G (n + 1) = (G (n + 1) + G (G n)) - G (G n) :=
        (add_then_sub (G (n + 1)) (G (G n))).symm
    _ = (n + 1) - G (G n) := by rw [the_loop_closes n]

theorem the_shadow_never_skips (n : Nat) :
    G (n + 1) = G n ∨ G (n + 1) = G n + 1 := by
  cases hl : lit (odometer n) with
  | true => exact Or.inl (click_holds_the_shadow (odometer n) (the_odometer_spaces n) hl)
  | false => exact Or.inr (click_moves_the_shadow (odometer n) (the_odometer_spaces n) hl)

theorem the_shadow_stays_awake : ∀ (n : Nat), 1 ≤ G (n + 1)
  | 0 => Nat.le_refl 1
  | n + 1 => by
      cases the_shadow_never_skips (n + 1) with
      | inl h => rw [h]; exact the_shadow_stays_awake n
      | inr h => rw [h]; exact Nat.succ_le_succ (Nat.zero_le (G (n + 1)))

theorem the_shadow_wakes_with_the_walker : ∀ (m : Nat), 1 ≤ m → 1 ≤ G m
  | m + 1, _ => the_shadow_stays_awake m
  | 0, h => nomatch h

theorem the_inner_call_is_grounded (n : Nat) : G (G n) ≤ n := by
  have hbal := the_two_shadows_balance n
  cases hl : lit (odometer n) with
  | false =>
      rw [hl] at hbal
      have h : G (G n) ≤ G n + G (G n) := Nat.le_add_left (G (G n)) (G n)
      rw [hbal] at h
      exact h
  | true =>
      rw [hl] at hbal
      have hone : 1 ≤ G n := a_lit_lamp_casts_a_shadow (odometer n) hl
      have h : 1 + G (G n) ≤ G n + G (G n) := Nat.add_le_add_right hone (G (G n))
      rw [hbal, Nat.add_comm 1 (G (G n))] at h
      exact Nat.le_of_succ_le_succ h

theorem the_seat_is_never_the_copy (n : Nat) : G (n + 2) < n + 2 := by
  have hinner : 1 ≤ G (G (n + 1)) :=
    the_shadow_wakes_with_the_walker (G (n + 1)) (the_shadow_stays_awake n)
  have h : G (n + 2) + 1 ≤ G (n + 2) + G (G (n + 1)) :=
    Nat.add_le_add_left hinner (G (n + 2))
  have hloop : G (n + 2) + G (G (n + 1)) = n + 2 := the_loop_closes (n + 1)
  rw [hloop] at h
  exact h

theorem fibN_matches_fib : ∀ (n : Nat), Int.ofNat (fibN n) = fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      show Int.ofNat (fibN (n + 1) + fibN n) = fib (n + 1) + fib n
      rw [← fibN_matches_fib (n + 1), ← fibN_matches_fib n]
      rfl

theorem worth_matches_zval : ∀ (ds : List Bool) (i : Nat),
    Int.ofNat (worth i ds) = zval i ds
  | [], _ => rfl
  | false :: rest, i => worth_matches_zval rest (i + 1)
  | true :: rest, i => by
      show Int.ofNat (fibN i + worth (i + 1) rest) = fib i + zval (i + 1) rest
      rw [← fibN_matches_fib i, ← worth_matches_zval rest (i + 1)]
      rfl

/-- info: 'Foam.Bridges.fibN_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms fibN_gnomon

/-- info: 'Foam.Bridges.worth_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms worth_gnomon

/-- info: 'Foam.Bridges.noconsec_tail' does not depend on any axioms -/
#guard_msgs in #print axioms noconsec_tail

/-- info: 'Foam.Bridges.noconsec_head' does not depend on any axioms -/
#guard_msgs in #print axioms noconsec_head

/-- info: 'Foam.Bridges.noconsec_false_cons' does not depend on any axioms -/
#guard_msgs in #print axioms noconsec_false_cons

/-- info: 'Foam.Bridges.carry_pays' does not depend on any axioms -/
#guard_msgs in #print axioms carry_pays

/-- info: 'Foam.Bridges.carry_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms carry_spaces

/-- info: 'Foam.Bridges.click_counts' does not depend on any axioms -/
#guard_msgs in #print axioms click_counts

/-- info: 'Foam.Bridges.click_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms click_spaces

/-- info: 'Foam.Bridges.click_holds_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms click_holds_the_shadow

/-- info: 'Foam.Bridges.click_moves_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms click_moves_the_shadow

/-- info: 'Foam.Bridges.a_lit_lamp_casts_a_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_lamp_casts_a_shadow

/-- info: 'Foam.Bridges.the_odometer_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms the_odometer_spaces

/-- info: 'Foam.Bridges.the_odometer_reads_true' does not depend on any axioms -/
#guard_msgs in #print axioms the_odometer_reads_true

/-- info: 'Foam.Bridges.g_hums_its_opening_bars' does not depend on any axioms -/
#guard_msgs in #print axioms g_hums_its_opening_bars

/-- info: 'Foam.Bridges.the_downshift_reads_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_downshift_reads_the_shadow

/-- info: 'Foam.Bridges.the_downshift_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms the_downshift_spaces

/-- info: 'Foam.Bridges.the_double_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_double_shadow

/-- info: 'Foam.Bridges.downshift_click_lit' does not depend on any axioms -/
#guard_msgs in #print axioms downshift_click_lit

/-- info: 'Foam.Bridges.downshift_click_unlit' does not depend on any axioms -/
#guard_msgs in #print axioms downshift_click_unlit

/-- info: 'Foam.Bridges.the_shadow_walks_the_downshift' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_walks_the_downshift

/-- info: 'Foam.Bridges.the_walker_carries_its_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_carries_its_shadow

/-- info: 'Foam.Bridges.the_shadow_never_outruns_the_walker' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_never_outruns_the_walker

/-- info: 'Foam.Bridges.the_two_shadows_balance' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_shadows_balance

/-- info: 'Foam.Bridges.the_loop_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_closes

/-- info: 'Foam.Bridges.sub_both_tick' does not depend on any axioms -/
#guard_msgs in #print axioms sub_both_tick

/-- info: 'Foam.Bridges.add_then_sub' does not depend on any axioms -/
#guard_msgs in #print axioms add_then_sub

/-- info: 'Foam.Bridges.the_grounded_object_satisfies_the_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_object_satisfies_the_loop

/-- info: 'Foam.Bridges.the_shadow_never_skips' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_never_skips

/-- info: 'Foam.Bridges.the_shadow_stays_awake' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_stays_awake

/-- info: 'Foam.Bridges.the_shadow_wakes_with_the_walker' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_wakes_with_the_walker

/-- info: 'Foam.Bridges.the_inner_call_is_grounded' does not depend on any axioms -/
#guard_msgs in #print axioms the_inner_call_is_grounded

/-- info: 'Foam.Bridges.the_seat_is_never_the_copy' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_is_never_the_copy

/-- info: 'Foam.Bridges.fibN_matches_fib' does not depend on any axioms -/
#guard_msgs in #print axioms fibN_matches_fib

/-- info: 'Foam.Bridges.worth_matches_zval' does not depend on any axioms -/
#guard_msgs in #print axioms worth_matches_zval

def capped : List Bool → Bool
  | [] => true
  | [false] => false
  | [true] => true
  | false :: d :: ds => capped (d :: ds)
  | true :: d :: ds => capped (d :: ds)

theorem capped_step (d e : Bool) (rest : List Bool) :
    capped (d :: e :: rest) = capped (e :: rest) := by
  cases d <;> rfl

theorem capped_true_cons : ∀ (ds : List Bool), capped (true :: ds) = capped ds
  | [] => rfl
  | d :: rest => capped_step true d rest

theorem capped_tail : ∀ {ds : List Bool}, capped (false :: ds) = true → capped ds = true
  | [], h => nomatch h
  | d :: rest, h => (capped_step false d rest).symm.trans h

theorem capped_tail_ne_nil : ∀ {ds : List Bool}, capped (false :: ds) = true → ds ≠ []
  | [], h => nomatch h
  | _ :: _, _ => fun heq => nomatch heq

theorem fibN_glows : ∀ (n : Nat), 1 ≤ fibN (n + 1)
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.le_trans (fibN_glows n) (Nat.le_add_right (fibN (n + 1)) (fibN n))

theorem a_capped_page_glows : ∀ (ds : List Bool) (i : Nat), capped ds = true → ds ≠ [] →
    1 ≤ worth (i + 1) ds
  | [], _, _, hne => absurd rfl hne
  | [true], i, _, _ => fibN_glows i
  | [false], _, hc, _ => nomatch hc
  | true :: d :: rest, i, _, _ =>
      Nat.le_trans (fibN_glows i) (Nat.le_add_right (fibN (i + 1)) (worth (i + 2) (d :: rest)))
  | false :: d :: rest, i, hc, _ =>
      a_capped_page_glows (d :: rest) (i + 1) (capped_tail hc) (fun heq => nomatch heq)

theorem carry_never_blanks : ∀ (ds : List Bool), carry ds ≠ []
  | [] => fun h => nomatch h
  | [_] => fun h => nomatch h
  | _ :: false :: _ => fun h => nomatch h
  | _ :: true :: _ => fun h => nomatch h

theorem carry_keeps_the_cap : ∀ (ds : List Bool), capped ds = true → capped (carry ds) = true
  | [], _ => rfl
  | [true], _ => rfl
  | [false], hc => nomatch hc
  | d :: false :: rest, hc => by
      show capped (true :: false :: rest) = true
      rw [capped_step] at hc ⊢
      exact hc
  | d :: true :: rest, hc => by
      show capped (false :: false :: carry rest) = true
      have hrest : capped rest = true := by
        rw [capped_step, capped_true_cons] at hc
        exact hc
      have hcap := carry_keeps_the_cap rest hrest
      cases hcr : carry rest with
      | nil => exact absurd hcr (carry_never_blanks rest)
      | cons c cs =>
          rw [hcr] at hcap
          rw [capped_step, capped_step]
          exact hcap

theorem click_keeps_the_cap : ∀ (ds : List Bool), capped ds = true → capped (click ds) = true
  | [], _ => rfl
  | false :: rest, hc => carry_keeps_the_cap (false :: rest) hc
  | true :: rest, hc => by
      show capped (false :: carry rest) = true
      have hrest : capped rest = true := by
        rw [capped_true_cons] at hc
        exact hc
      have hcap := carry_keeps_the_cap rest hrest
      cases hcr : carry rest with
      | nil => exact absurd hcr (carry_never_blanks rest)
      | cons c cs =>
          rw [hcr] at hcap
          rw [capped_step]
          exact hcap

theorem the_odometer_wastes_no_seats : ∀ (n : Nat), capped (odometer n) = true
  | 0 => rfl
  | n + 1 => click_keeps_the_cap (odometer n) (the_odometer_wastes_no_seats n)

def ripple : List Bool → List Bool
  | [] => [false, true]
  | false :: tail => false :: true :: false :: tail
  | true :: tail => true :: false :: true :: tail

def unclick : List Bool → List Bool
  | [] => []
  | [true] => []
  | [false] => []
  | true :: d :: ds => false :: d :: ds
  | [false, true] => [true]
  | false :: true :: d :: ds => true :: false :: d :: ds
  | false :: false :: ds => ripple (unclick ds)

theorem unclick_spaces : ∀ (ds : List Bool), NoConsec ds → NoConsec (unclick ds)
  | [], _ => True.intro
  | [true], _ => True.intro
  | [false], _ => True.intro
  | true :: false :: _, h => h
  | true :: true :: _, h => h.elim
  | [false, true], _ => True.intro
  | false :: true :: false :: _, h => h
  | false :: true :: true :: _, h => h.elim
  | false :: false :: rest, h => by
      have ih := unclick_spaces rest (noconsec_tail (noconsec_tail h))
      show NoConsec (ripple (unclick rest))
      cases hu : unclick rest with
      | nil => exact True.intro
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true => exact ih
          | false => exact ih

theorem unclick_keeps_the_cap : ∀ (ds : List Bool), capped ds = true →
    capped (unclick ds) = true
  | [], _ => rfl
  | [true], _ => rfl
  | [false], hc => nomatch hc
  | true :: d :: rest, hc => by
      show capped (false :: d :: rest) = true
      rw [capped_step] at hc ⊢
      exact hc
  | [false, true], _ => rfl
  | false :: true :: d :: rest, hc => by
      show capped (true :: false :: d :: rest) = true
      rw [capped_step, capped_step] at hc ⊢
      exact hc
  | false :: false :: rest, hc => by
      have ih := unclick_keeps_the_cap rest (capped_tail (capped_tail hc))
      show capped (ripple (unclick rest)) = true
      cases hu : unclick rest with
      | nil => rfl
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true =>
              show capped (true :: false :: true :: tail) = true
              rw [capped_step, capped_step]
              exact ih
          | false =>
              show capped (false :: true :: false :: tail) = true
              rw [capped_step, capped_step]
              exact ih

theorem add_swap_right (a b c : Nat) : (a + b) + c = (a + c) + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

theorem unclick_pays : ∀ (ds : List Bool) (i : Nat), capped ds = true → ds ≠ [] →
    worth (i + 1) (unclick ds) + cond (lit (unclick ds)) (fibN i) (fibN (i + 1))
      = worth (i + 1) ds
  | [], _, _, hne => absurd rfl hne
  | [true], i, _, _ => Nat.zero_add (fibN (i + 1))
  | [false], _, hc, _ => nomatch hc
  | true :: d :: rest, i, _, _ => Nat.add_comm (worth (i + 2) (d :: rest)) (fibN (i + 1))
  | [false, true], i, _, _ => (fibN_gnomon i).symm
  | false :: true :: d :: rest, i, _, _ => by
      show (fibN (i + 1) + worth (i + 3) (d :: rest)) + fibN i
        = fibN (i + 2) + worth (i + 3) (d :: rest)
      rw [add_swap_right, ← fibN_gnomon]
  | false :: false :: rest, i, hc, _ => by
      have hrest : capped rest = true := capped_tail (capped_tail hc)
      have hne : rest ≠ [] := capped_tail_ne_nil (capped_tail hc)
      have ih := unclick_pays rest (i + 2) hrest hne
      show worth (i + 1) (ripple (unclick rest))
          + cond (lit (ripple (unclick rest))) (fibN i) (fibN (i + 1))
        = worth (i + 3) rest
      cases hu : unclick rest with
      | nil =>
          rw [hu] at ih
          have ih' : fibN (i + 3) = worth (i + 3) rest :=
            (Nat.zero_add (fibN (i + 3))).symm.trans ih
          show fibN (i + 2) + fibN (i + 1) = worth (i + 3) rest
          rw [← ih']
          exact (fibN_gnomon (i + 1)).symm
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true =>
              show (fibN (i + 1) + worth (i + 3) (true :: tail)) + fibN i
                = worth (i + 3) rest
              rw [add_swap_right, ← fibN_gnomon, Nat.add_comm]
              exact ih
          | false =>
              show (fibN (i + 2) + worth (i + 4) tail) + fibN (i + 1)
                = worth (i + 3) rest
              rw [add_swap_right, ← fibN_gnomon, Nat.add_comm]
              exact ih

theorem unclick_counts (ds : List Bool) (hc : capped ds = true) (hne : ds ≠ []) :
    worth 2 (unclick ds) + 1 = worth 2 ds := by
  have hp := unclick_pays ds 1 hc hne
  cases hl : lit (unclick ds) with
  | true => rw [hl] at hp; exact hp
  | false => rw [hl] at hp; exact hp

theorem the_click_comes_home : ∀ (ds : List Bool), NoConsec ds → capped ds = true →
    ds ≠ [] → click (unclick ds) = ds
  | [], _, _, hne => absurd rfl hne
  | [true], _, _, _ => rfl
  | [false], _, hc, _ => nomatch hc
  | true :: false :: _, _, _, _ => rfl
  | true :: true :: _, h, _, _ => h.elim
  | [false, true], _, _, _ => rfl
  | false :: true :: false :: _, _, _, _ => rfl
  | false :: true :: true :: _, h, _, _ => h.elim
  | false :: false :: rest, h, hc, _ => by
      have ih := the_click_comes_home rest (noconsec_tail (noconsec_tail h))
        (capped_tail (capped_tail hc)) (capped_tail_ne_nil (capped_tail hc))
      show click (ripple (unclick rest)) = false :: false :: rest
      cases hu : unclick rest with
      | nil =>
          rw [hu] at ih
          exact congrArg (fun t => false :: false :: t) ih
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true => exact congrArg (fun t => false :: false :: t) ih
          | false => exact congrArg (fun t => false :: false :: t) ih

theorem the_odometer_is_the_only_spaced_page : ∀ (n : Nat) (ds : List Bool),
    NoConsec ds → capped ds = true → worth 2 ds = n → ds = odometer n
  | 0, [], _, _, _ => rfl
  | 0, d :: rest, _, hc, hw => by
      have hg : 1 ≤ worth 2 (d :: rest) :=
        a_capped_page_glows (d :: rest) 1 hc (fun heq => nomatch heq)
      rw [hw] at hg
      exact absurd hg (Nat.not_succ_le_zero 0)
  | n + 1, ds, hnc, hc, hw => by
      have hne : ds ≠ [] := by
        intro heq
        rw [heq] at hw
        exact nomatch hw
      have hstep : worth 2 (unclick ds) + 1 = n + 1 := by
        rw [← hw]
        exact unclick_counts ds hc hne
      have hind := the_odometer_is_the_only_spaced_page n (unclick ds)
        (unclick_spaces ds hnc) (unclick_keeps_the_cap ds hc) (Nat.succ.inj hstep)
      have hcome := the_click_comes_home ds hnc hc hne
      rw [← hcome, hind]
      rfl

theorem every_spaced_page_is_a_reading (ds : List Bool) (hnc : NoConsec ds)
    (hc : capped ds = true) : ds = odometer (worth 2 ds) :=
  the_odometer_is_the_only_spaced_page (worth 2 ds) ds hnc hc rfl

theorem two_spaced_pages_of_one_worth_are_one_page (ds es : List Bool)
    (hnds : NoConsec ds) (hnes : NoConsec es)
    (hcds : capped ds = true) (hces : capped es = true)
    (hw : worth 2 ds = worth 2 es) : ds = es :=
  (the_odometer_is_the_only_spaced_page (worth 2 es) ds hnds hcds hw).trans
    (the_odometer_is_the_only_spaced_page (worth 2 es) es hnes hces rfl).symm

def beacon : Nat → List Bool
  | 0 => [true]
  | k + 1 => false :: beacon k

theorem the_beacon_never_blanks : ∀ (k : Nat), beacon k ≠ []
  | 0 => fun h => nomatch h
  | _ + 1 => fun h => nomatch h

theorem the_beacon_spaces : ∀ (k : Nat), NoConsec (beacon k)
  | 0 => True.intro
  | k + 1 => noconsec_false_cons (the_beacon_spaces k)

theorem the_beacon_wears_the_cap : ∀ (k : Nat), capped (beacon k) = true
  | 0 => rfl
  | k + 1 => by
      show capped (false :: beacon k) = true
      cases hbk : beacon k with
      | nil => exact absurd hbk (the_beacon_never_blanks k)
      | cons b bs =>
          rw [capped_step, ← hbk]
          exact the_beacon_wears_the_cap k

theorem a_beacon_is_one_lamp : ∀ (k i : Nat), worth i (beacon k) = fibN (i + k)
  | 0, _ => rfl
  | k + 1, i => by
      show worth (i + 1) (beacon k) = fibN (i + (k + 1))
      rw [a_beacon_is_one_lamp k (i + 1)]
      exact congrArg fibN ((Nat.succ_add i k).trans (Nat.add_succ i k).symm)

theorem the_odometer_at_a_fibonacci_is_a_beacon (k : Nat) :
    odometer (fibN (k + 2)) = beacon k :=
  (the_odometer_is_the_only_spaced_page (fibN (k + 2)) (beacon k) (the_beacon_spaces k)
    (the_beacon_wears_the_cap k)
    ((a_beacon_is_one_lamp k 2).trans (congrArg fibN (Nat.add_comm 2 k)))).symm

theorem the_beacon_slides_one_seat_down (k : Nat) : G (fibN (k + 2)) = fibN (k + 1) := by
  show worth 1 (odometer (fibN (k + 2))) = fibN (k + 1)
  rw [the_odometer_at_a_fibonacci_is_a_beacon k, a_beacon_is_one_lamp k 1]
  exact congrArg fibN (Nat.add_comm 1 k)

theorem the_beacon_downshifts_to_the_beacon_below (k : Nat) :
    downshift (beacon (k + 1)) = beacon k := rfl

theorem the_bottom_beacon_holds : downshift (beacon 0) = beacon 0 := rfl

theorem g_hums_the_fibonacci_stairs :
    (G 1, G 2, G 3, G 5, G 8, G 13, G 21) = (1, 1, 2, 3, 5, 8, 13) := rfl

/-- info: 'Foam.Bridges.capped_step' does not depend on any axioms -/
#guard_msgs in #print axioms capped_step

/-- info: 'Foam.Bridges.capped_true_cons' does not depend on any axioms -/
#guard_msgs in #print axioms capped_true_cons

/-- info: 'Foam.Bridges.capped_tail' does not depend on any axioms -/
#guard_msgs in #print axioms capped_tail

/-- info: 'Foam.Bridges.capped_tail_ne_nil' does not depend on any axioms -/
#guard_msgs in #print axioms capped_tail_ne_nil

/-- info: 'Foam.Bridges.fibN_glows' does not depend on any axioms -/
#guard_msgs in #print axioms fibN_glows

/-- info: 'Foam.Bridges.a_capped_page_glows' does not depend on any axioms -/
#guard_msgs in #print axioms a_capped_page_glows

/-- info: 'Foam.Bridges.carry_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms carry_never_blanks

/-- info: 'Foam.Bridges.carry_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms carry_keeps_the_cap

/-- info: 'Foam.Bridges.click_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms click_keeps_the_cap

/-- info: 'Foam.Bridges.the_odometer_wastes_no_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_odometer_wastes_no_seats

/-- info: 'Foam.Bridges.unclick_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms unclick_spaces

/-- info: 'Foam.Bridges.unclick_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms unclick_keeps_the_cap

/-- info: 'Foam.Bridges.add_swap_right' does not depend on any axioms -/
#guard_msgs in #print axioms add_swap_right

/-- info: 'Foam.Bridges.unclick_pays' does not depend on any axioms -/
#guard_msgs in #print axioms unclick_pays

/-- info: 'Foam.Bridges.unclick_counts' does not depend on any axioms -/
#guard_msgs in #print axioms unclick_counts

/-- info: 'Foam.Bridges.the_click_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_click_comes_home

/-- info: 'Foam.Bridges.the_odometer_is_the_only_spaced_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_odometer_is_the_only_spaced_page

/-- info: 'Foam.Bridges.every_spaced_page_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms every_spaced_page_is_a_reading

/-- info: 'Foam.Bridges.two_spaced_pages_of_one_worth_are_one_page' does not depend on any axioms -/
#guard_msgs in #print axioms two_spaced_pages_of_one_worth_are_one_page

/-- info: 'Foam.Bridges.the_beacon_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_never_blanks

/-- info: 'Foam.Bridges.the_beacon_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_spaces

/-- info: 'Foam.Bridges.the_beacon_wears_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_wears_the_cap

/-- info: 'Foam.Bridges.a_beacon_is_one_lamp' does not depend on any axioms -/
#guard_msgs in #print axioms a_beacon_is_one_lamp

/-- info: 'Foam.Bridges.the_odometer_at_a_fibonacci_is_a_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_odometer_at_a_fibonacci_is_a_beacon

/-- info: 'Foam.Bridges.the_beacon_slides_one_seat_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_slides_one_seat_down

/-- info: 'Foam.Bridges.the_beacon_downshifts_to_the_beacon_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_downshifts_to_the_beacon_below

/-- info: 'Foam.Bridges.the_bottom_beacon_holds' does not depend on any axioms -/
#guard_msgs in #print axioms the_bottom_beacon_holds

/-- info: 'Foam.Bridges.g_hums_the_fibonacci_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms g_hums_the_fibonacci_stairs

def hcarry : List Bool → List Bool
  | [] => [true]
  | [_] => [true]
  | [_, _] => [true]
  | _ :: _ :: false :: rest => true :: false :: false :: rest
  | _ :: _ :: true :: rest => false :: false :: false :: hcarry rest

theorem hcarry_pays : ∀ (ds : List Bool) (i : Nat), Sparse ds → clearing ds = true →
    graze i (hcarry ds) = herdN i + graze i ds
  | [], _, _, _ => rfl
  | [false], _, _, _ => rfl
  | true :: _, _, _, hcl => nomatch hcl
  | [false, false], _, _, _ => rfl
  | [false, true], _, _, hcl => nomatch hcl
  | false :: true :: _ :: _, _, _, hcl => nomatch hcl
  | false :: false :: false :: _, _, _, _ => rfl
  | false :: false :: true :: rest, i, h, _ => by
      show graze (i + 3) (hcarry rest)
        = herdN i + (herdN (i + 2) + graze (i + 3) rest)
      rw [hcarry_pays rest (i + 3) (sparse_tail (sparse_tail (sparse_tail h)))
            (sparse_head (sparse_tail (sparse_tail h))),
          ← Nat.add_assoc (herdN i) (herdN (i + 2)) (graze (i + 3) rest),
          Nat.add_comm (herdN i) (herdN (i + 2)), ← herdN_gnomon]

theorem hcarry_spaces : ∀ (ds : List Bool), Sparse ds → clearing ds = true →
    Sparse (hcarry ds)
  | [], _, _ => True.intro
  | [false], _, _ => True.intro
  | true :: _, _, hcl => nomatch hcl
  | [false, false], _, _ => True.intro
  | [false, true], _, hcl => nomatch hcl
  | false :: true :: _ :: _, _, hcl => nomatch hcl
  | false :: false :: false :: _, h, _ => h
  | false :: false :: true :: rest, h, _ =>
      hcarry_spaces rest (sparse_tail (sparse_tail (sparse_tail h)))
        (sparse_head (sparse_tail (sparse_tail h)))

def hclick : List Bool → List Bool
  | [] => [true]
  | [false] => [true]
  | false :: false :: rest => hcarry (false :: false :: rest)
  | false :: true :: rest => false :: false :: hcarry rest
  | true :: rest => false :: hcarry rest

theorem hclick_counts : ∀ (ds : List Bool), Sparse ds →
    graze 3 (hclick ds) = graze 3 ds + 1
  | [], _ => rfl
  | [false], _ => rfl
  | false :: false :: rest, h => by
      show graze 3 (hcarry (false :: false :: rest)) = graze 3 (false :: false :: rest) + 1
      rw [hcarry_pays (false :: false :: rest) 3 h rfl]
      exact Nat.add_comm 1 (graze 3 (false :: false :: rest))
  | false :: true :: rest, h => by
      show graze 5 (hcarry rest) = (herdN 4 + graze 5 rest) + 1
      rw [hcarry_pays rest 5 (sparse_tail (sparse_tail h)) (sparse_head (sparse_tail h))]
      show 3 + graze 5 rest = (2 + graze 5 rest) + 1
      rw [Nat.add_comm 2 (graze 5 rest)]
      exact Nat.add_comm 3 (graze 5 rest)
  | true :: rest, h => by
      show graze 4 (hcarry rest) = (herdN 3 + graze 4 rest) + 1
      rw [hcarry_pays rest 4 (sparse_tail h) (sparse_head h)]
      show 2 + graze 4 rest = (1 + graze 4 rest) + 1
      rw [Nat.add_comm 1 (graze 4 rest)]
      exact Nat.add_comm 2 (graze 4 rest)

theorem hclick_spaces : ∀ (ds : List Bool), Sparse ds → Sparse (hclick ds)
  | [], _ => True.intro
  | [false], _ => True.intro
  | false :: false :: rest, h => hcarry_spaces (false :: false :: rest) h rfl
  | false :: true :: rest, h =>
      hcarry_spaces rest (sparse_tail (sparse_tail h)) (sparse_head (sparse_tail h))
  | true :: rest, h => hcarry_spaces rest (sparse_tail h) (sparse_head h)

theorem hclick_holds_the_shadow : ∀ (ds : List Bool), Sparse ds → lit ds = true →
    graze 2 (hclick ds) = graze 2 ds
  | [], _, hl => nomatch hl
  | false :: _, _, hl => nomatch hl
  | true :: rest, h, _ => by
      show graze 3 (hcarry rest) = herdN 2 + graze 3 rest
      rw [hcarry_pays rest 3 (sparse_tail h) (sparse_head h)]
      rfl

theorem hclick_moves_the_shadow : ∀ (ds : List Bool), Sparse ds → lit ds = false →
    graze 2 (hclick ds) = graze 2 ds + 1
  | [], _, _ => rfl
  | [false], _, _ => rfl
  | false :: false :: rest, h, _ => by
      show graze 2 (hcarry (false :: false :: rest)) = graze 2 (false :: false :: rest) + 1
      rw [hcarry_pays (false :: false :: rest) 2 h rfl]
      exact Nat.add_comm 1 (graze 2 (false :: false :: rest))
  | false :: true :: rest, h, _ => by
      show graze 4 (hcarry rest) = (herdN 3 + graze 4 rest) + 1
      rw [hcarry_pays rest 4 (sparse_tail (sparse_tail h)) (sparse_head (sparse_tail h))]
      show 2 + graze 4 rest = (1 + graze 4 rest) + 1
      rw [Nat.add_comm 1 (graze 4 rest)]
      exact Nat.add_comm 2 (graze 4 rest)
  | true :: _, _, hl => nomatch hl

theorem a_lit_lamp_casts_a_long_shadow : ∀ (ds : List Bool), lit ds = true →
    1 ≤ graze 2 ds
  | true :: rest, _ => Nat.le_add_right 1 (graze 3 rest)
  | [], hl => nomatch hl
  | false :: _, hl => nomatch hl

def hodometer : Nat → List Bool
  | 0 => []
  | n + 1 => hclick (hodometer n)

theorem the_hodometer_spaces : ∀ (n : Nat), Sparse (hodometer n)
  | 0 => True.intro
  | n + 1 => hclick_spaces (hodometer n) (the_hodometer_spaces n)

theorem the_hodometer_reads_true : ∀ (n : Nat), graze 3 (hodometer n) = n
  | 0 => rfl
  | n + 1 => by
      show graze 3 (hclick (hodometer n)) = n + 1
      rw [hclick_counts (hodometer n) (the_hodometer_spaces n),
          the_hodometer_reads_true n]

def H (n : Nat) : Nat := graze 2 (hodometer n)

theorem h_hums_its_opening_bars :
    (H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7) = (0, 1, 1, 2, 3, 4, 4, 5) := rfl

def hdownshift : List Bool → List Bool
  | [] => []
  | false :: rest => rest
  | true :: rest => hcarry rest

theorem the_hdownshift_reads_the_shadow : ∀ (ds : List Bool), Sparse ds →
    graze 3 (hdownshift ds) = graze 2 ds
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: rest, h => by
      show graze 3 (hcarry rest) = herdN 2 + graze 3 rest
      rw [hcarry_pays rest 3 (sparse_tail h) (sparse_head h)]
      rfl

theorem the_hdownshift_reads_the_second_shadow : ∀ (ds : List Bool), Sparse ds →
    graze 2 (hdownshift ds) = graze 1 ds
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: rest, h => by
      show graze 2 (hcarry rest) = herdN 1 + graze 2 rest
      rw [hcarry_pays rest 2 (sparse_tail h) (sparse_head h)]
      rfl

theorem the_hdownshift_spaces : ∀ (ds : List Bool), Sparse ds → Sparse (hdownshift ds)
  | [], _ => True.intro
  | false :: _, h => sparse_tail h
  | true :: rest, h => hcarry_spaces rest (sparse_tail h) (sparse_head h)

theorem the_triple_shadow : ∀ (ds : List Bool), Sparse ds →
    graze 1 (hdownshift ds) = graze 0 ds + cond (lit ds) 1 0
  | [], _ => rfl
  | false :: _, _ => rfl
  | true :: rest, h => by
      show graze 1 (hcarry rest) = (herdN 0 + graze 1 rest) + 1
      rw [hcarry_pays rest 1 (sparse_tail h) (sparse_head h)]
      show 1 + graze 1 rest = (0 + graze 1 rest) + 1
      rw [Nat.zero_add]
      exact Nat.add_comm 1 (graze 1 rest)

theorem hdownshift_hclick_lit : ∀ (ds : List Bool), lit ds = true →
    hdownshift (hclick ds) = hdownshift ds
  | [], hl => nomatch hl
  | false :: _, hl => nomatch hl
  | true :: _, _ => rfl

theorem hdownshift_hclick_unlit : ∀ (ds : List Bool), lit ds = false →
    hdownshift (hclick ds) = hclick (hdownshift ds)
  | [], _ => rfl
  | [false], _ => rfl
  | [false, false], _ => rfl
  | false :: false :: false :: _, _ => rfl
  | false :: false :: true :: _, _ => rfl
  | false :: true :: _, _ => rfl
  | true :: _, hl => nomatch hl

theorem the_shadow_walks_the_hdownshift : ∀ (n : Nat),
    hodometer (H n) = hdownshift (hodometer n)
  | 0 => rfl
  | n + 1 => by
      cases hl : lit (hodometer n) with
      | true =>
          show hodometer (graze 2 (hclick (hodometer n)))
            = hdownshift (hclick (hodometer n))
          rw [hclick_holds_the_shadow (hodometer n) (the_hodometer_spaces n) hl,
              hdownshift_hclick_lit (hodometer n) hl]
          exact the_shadow_walks_the_hdownshift n
      | false =>
          show hodometer (graze 2 (hclick (hodometer n)))
            = hdownshift (hclick (hodometer n))
          rw [hclick_moves_the_shadow (hodometer n) (the_hodometer_spaces n) hl,
              hdownshift_hclick_unlit (hodometer n) hl]
          exact congrArg hclick (the_shadow_walks_the_hdownshift n)

theorem the_drover_carries_its_shadow (n : Nat) : H n + graze 0 (hodometer n) = n :=
  ((the_hodometer_reads_true n).symm.trans (graze_gnomon (hodometer n) 0)).symm

theorem the_shadow_never_outruns_the_drover (n : Nat) : H n ≤ n :=
  Nat.le.intro (the_drover_carries_its_shadow n)

theorem the_second_shadow_reads_one_down (n : Nat) : H (H n) = graze 1 (hodometer n) := by
  show graze 2 (hodometer (H n)) = graze 1 (hodometer n)
  rw [the_shadow_walks_the_hdownshift n]
  exact the_hdownshift_reads_the_second_shadow (hodometer n) (the_hodometer_spaces n)

theorem the_third_shadow_reads_the_ground (n : Nat) :
    H (H (H n)) = graze 0 (hodometer n) + cond (lit (hodometer n)) 1 0 := by
  show graze 2 (hodometer (H (H n)))
    = graze 0 (hodometer n) + cond (lit (hodometer n)) 1 0
  rw [the_shadow_walks_the_hdownshift (H n), the_shadow_walks_the_hdownshift n,
      the_hdownshift_reads_the_second_shadow (hdownshift (hodometer n))
        (the_hdownshift_spaces (hodometer n) (the_hodometer_spaces n))]
  exact the_triple_shadow (hodometer n) (the_hodometer_spaces n)

theorem the_three_shadows_balance (n : Nat) :
    H n + H (H (H n)) = n + cond (lit (hodometer n)) 1 0 := by
  rw [the_third_shadow_reads_the_ground n,
      ← Nat.add_assoc (H n) (graze 0 (hodometer n)) (cond (lit (hodometer n)) 1 0),
      the_drover_carries_its_shadow n]

theorem the_deeper_loop_closes (n : Nat) : H (n + 1) + H (H (H n)) = n + 1 := by
  cases hl : lit (hodometer n) with
  | true =>
      have hstep : H (n + 1) = H n :=
        hclick_holds_the_shadow (hodometer n) (the_hodometer_spaces n) hl
      have hbal := the_three_shadows_balance n
      rw [hl] at hbal
      rw [hstep]
      exact hbal
  | false =>
      have hstep : H (n + 1) = H n + 1 :=
        hclick_moves_the_shadow (hodometer n) (the_hodometer_spaces n) hl
      have hbal := the_three_shadows_balance n
      rw [hl] at hbal
      rw [hstep, Nat.add_comm (H n) 1, Nat.add_assoc]
      show 1 + (H n + H (H (H n))) = n + 1
      rw [hbal]
      exact Nat.add_comm 1 n

theorem the_grounded_object_satisfies_the_deeper_loop (n : Nat) :
    H (n + 1) = (n + 1) - H (H (H n)) :=
  calc H (n + 1) = (H (n + 1) + H (H (H n))) - H (H (H n)) :=
        (add_then_sub (H (n + 1)) (H (H (H n)))).symm
    _ = (n + 1) - H (H (H n)) := by rw [the_deeper_loop_closes n]

theorem the_drovers_shadow_never_skips (n : Nat) :
    H (n + 1) = H n ∨ H (n + 1) = H n + 1 := by
  cases hl : lit (hodometer n) with
  | true =>
      exact Or.inl (hclick_holds_the_shadow (hodometer n) (the_hodometer_spaces n) hl)
  | false =>
      exact Or.inr (hclick_moves_the_shadow (hodometer n) (the_hodometer_spaces n) hl)

theorem the_drovers_shadow_stays_awake : ∀ (n : Nat), 1 ≤ H (n + 1)
  | 0 => Nat.le_refl 1
  | n + 1 => by
      cases the_drovers_shadow_never_skips (n + 1) with
      | inl h => rw [h]; exact the_drovers_shadow_stays_awake n
      | inr h => rw [h]; exact Nat.succ_le_succ (Nat.zero_le (H (n + 1)))

theorem the_shadow_wakes_with_the_drover : ∀ (m : Nat), 1 ≤ m → 1 ≤ H m
  | m + 1, _ => the_drovers_shadow_stays_awake m
  | 0, h => nomatch h

theorem the_middle_call_is_grounded (n : Nat) : H (H n) ≤ n :=
  Nat.le_trans (the_shadow_never_outruns_the_drover (H n))
    (the_shadow_never_outruns_the_drover n)

theorem the_innermost_call_is_grounded (n : Nat) : H (H (H n)) ≤ n := by
  have hbal := the_three_shadows_balance n
  cases hl : lit (hodometer n) with
  | false =>
      rw [hl] at hbal
      have h : H (H (H n)) ≤ H n + H (H (H n)) :=
        Nat.le_add_left (H (H (H n))) (H n)
      rw [hbal] at h
      exact h
  | true =>
      rw [hl] at hbal
      have hone : 1 ≤ H n := a_lit_lamp_casts_a_long_shadow (hodometer n) hl
      have h : 1 + H (H (H n)) ≤ H n + H (H (H n)) :=
        Nat.add_le_add_right hone (H (H (H n)))
      rw [hbal, Nat.add_comm 1 (H (H (H n)))] at h
      exact Nat.le_of_succ_le_succ h

theorem the_drovers_seat_is_never_the_copy (n : Nat) : H (n + 2) < n + 2 := by
  have hinner : 1 ≤ H (H (H (n + 1))) :=
    the_shadow_wakes_with_the_drover (H (H (n + 1)))
      (the_shadow_wakes_with_the_drover (H (n + 1)) (the_drovers_shadow_stays_awake n))
  have h : H (n + 2) + 1 ≤ H (n + 2) + H (H (H (n + 1))) :=
    Nat.add_le_add_left hinner (H (n + 2))
  have hloop : H (n + 2) + H (H (H (n + 1))) = n + 2 := the_deeper_loop_closes (n + 1)
  rw [hloop] at h
  exact h

theorem h_hums_the_herd_stairs :
    (H 1, H 2, H 3, H 4, H 6, H 9, H 13, H 19) = (1, 1, 2, 3, 4, 6, 9, 13) := rfl

/-- info: 'Foam.Bridges.hcarry_pays' does not depend on any axioms -/
#guard_msgs in #print axioms hcarry_pays

/-- info: 'Foam.Bridges.hcarry_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms hcarry_spaces

/-- info: 'Foam.Bridges.hclick_counts' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_counts

/-- info: 'Foam.Bridges.hclick_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_spaces

/-- info: 'Foam.Bridges.hclick_holds_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_holds_the_shadow

/-- info: 'Foam.Bridges.hclick_moves_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_moves_the_shadow

/-- info: 'Foam.Bridges.a_lit_lamp_casts_a_long_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_lamp_casts_a_long_shadow

/-- info: 'Foam.Bridges.the_hodometer_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms the_hodometer_spaces

/-- info: 'Foam.Bridges.the_hodometer_reads_true' does not depend on any axioms -/
#guard_msgs in #print axioms the_hodometer_reads_true

/-- info: 'Foam.Bridges.h_hums_its_opening_bars' does not depend on any axioms -/
#guard_msgs in #print axioms h_hums_its_opening_bars

/-- info: 'Foam.Bridges.the_hdownshift_reads_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_hdownshift_reads_the_shadow

/-- info: 'Foam.Bridges.the_hdownshift_reads_the_second_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_hdownshift_reads_the_second_shadow

/-- info: 'Foam.Bridges.the_hdownshift_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms the_hdownshift_spaces

/-- info: 'Foam.Bridges.the_triple_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_triple_shadow

/-- info: 'Foam.Bridges.hdownshift_hclick_lit' does not depend on any axioms -/
#guard_msgs in #print axioms hdownshift_hclick_lit

/-- info: 'Foam.Bridges.hdownshift_hclick_unlit' does not depend on any axioms -/
#guard_msgs in #print axioms hdownshift_hclick_unlit

/-- info: 'Foam.Bridges.the_shadow_walks_the_hdownshift' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_walks_the_hdownshift

/-- info: 'Foam.Bridges.the_drover_carries_its_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_carries_its_shadow

/-- info: 'Foam.Bridges.the_shadow_never_outruns_the_drover' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_never_outruns_the_drover

/-- info: 'Foam.Bridges.the_second_shadow_reads_one_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_shadow_reads_one_down

/-- info: 'Foam.Bridges.the_third_shadow_reads_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_third_shadow_reads_the_ground

/-- info: 'Foam.Bridges.the_three_shadows_balance' does not depend on any axioms -/
#guard_msgs in #print axioms the_three_shadows_balance

/-- info: 'Foam.Bridges.the_deeper_loop_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_deeper_loop_closes

/-- info: 'Foam.Bridges.the_grounded_object_satisfies_the_deeper_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_object_satisfies_the_deeper_loop

/-- info: 'Foam.Bridges.the_drovers_shadow_never_skips' does not depend on any axioms -/
#guard_msgs in #print axioms the_drovers_shadow_never_skips

/-- info: 'Foam.Bridges.the_drovers_shadow_stays_awake' does not depend on any axioms -/
#guard_msgs in #print axioms the_drovers_shadow_stays_awake

/-- info: 'Foam.Bridges.the_shadow_wakes_with_the_drover' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_wakes_with_the_drover

/-- info: 'Foam.Bridges.the_middle_call_is_grounded' does not depend on any axioms -/
#guard_msgs in #print axioms the_middle_call_is_grounded

/-- info: 'Foam.Bridges.the_innermost_call_is_grounded' does not depend on any axioms -/
#guard_msgs in #print axioms the_innermost_call_is_grounded

/-- info: 'Foam.Bridges.the_drovers_seat_is_never_the_copy' does not depend on any axioms -/
#guard_msgs in #print axioms the_drovers_seat_is_never_the_copy

/-- info: 'Foam.Bridges.h_hums_the_herd_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms h_hums_the_herd_stairs

theorem a_capped_page_grazes : ∀ (ds : List Bool) (i : Nat), capped ds = true → ds ≠ [] →
    1 ≤ graze (i + 1) ds
  | [], _, _, hne => absurd rfl hne
  | [true], i, _, _ => herdN_glows i
  | [false], _, hc, _ => nomatch hc
  | true :: d :: rest, i, _, _ =>
      Nat.le_trans (herdN_glows i)
        (Nat.le_add_right (herdN (i + 1)) (graze (i + 2) (d :: rest)))
  | false :: d :: rest, i, hc, _ =>
      a_capped_page_grazes (d :: rest) (i + 1) (capped_tail hc) (fun heq => nomatch heq)

theorem hcarry_never_blanks : ∀ (ds : List Bool), hcarry ds ≠ []
  | [] => fun h => nomatch h
  | [_] => fun h => nomatch h
  | [_, _] => fun h => nomatch h
  | _ :: _ :: false :: _ => fun h => nomatch h
  | _ :: _ :: true :: _ => fun h => nomatch h

theorem hcarry_keeps_the_cap : ∀ (ds : List Bool), capped ds = true →
    capped (hcarry ds) = true
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | d :: e :: false :: rest, hc => by
      show capped (true :: false :: false :: rest) = true
      rw [capped_step, capped_step] at hc
      rw [capped_step, capped_step]
      exact hc
  | d :: e :: true :: rest, hc => by
      show capped (false :: false :: false :: hcarry rest) = true
      have hrest : capped rest = true := by
        rw [capped_step, capped_step, capped_true_cons] at hc
        exact hc
      have hcap := hcarry_keeps_the_cap rest hrest
      cases hcr : hcarry rest with
      | nil => exact absurd hcr (hcarry_never_blanks rest)
      | cons c cs =>
          rw [hcr] at hcap
          rw [capped_step, capped_step, capped_step]
          exact hcap

theorem hclick_keeps_the_cap : ∀ (ds : List Bool), capped ds = true →
    capped (hclick ds) = true
  | [], _ => rfl
  | [false], _ => rfl
  | false :: false :: rest, hc => hcarry_keeps_the_cap (false :: false :: rest) hc
  | false :: true :: rest, hc => by
      show capped (false :: false :: hcarry rest) = true
      have hrest : capped rest = true := by
        rw [capped_step, capped_true_cons] at hc
        exact hc
      have hcap := hcarry_keeps_the_cap rest hrest
      cases hcr : hcarry rest with
      | nil => exact absurd hcr (hcarry_never_blanks rest)
      | cons c cs =>
          rw [hcr] at hcap
          rw [capped_step, capped_step]
          exact hcap
  | true :: rest, hc => by
      show capped (false :: hcarry rest) = true
      have hrest : capped rest = true := by
        rw [capped_true_cons] at hc
        exact hc
      have hcap := hcarry_keeps_the_cap rest hrest
      cases hcr : hcarry rest with
      | nil => exact absurd hcr (hcarry_never_blanks rest)
      | cons c cs =>
          rw [hcr] at hcap
          rw [capped_step]
          exact hcap

theorem the_hodometer_wastes_no_seats : ∀ (n : Nat), capped (hodometer n) = true
  | 0 => rfl
  | n + 1 => hclick_keeps_the_cap (hodometer n) (the_hodometer_wastes_no_seats n)

def hripple : List Bool → List Bool
  | [] => [false, false, true]
  | [false] => [false, false, true, false]
  | true :: tail => true :: false :: false :: true :: tail
  | false :: true :: tail => false :: true :: false :: false :: true :: tail
  | false :: false :: tail => false :: false :: true :: false :: false :: tail

def hunclick : List Bool → List Bool
  | [] => []
  | [true] => []
  | [false] => []
  | true :: d :: ds => false :: d :: ds
  | [false, true] => [true]
  | false :: true :: d :: ds => true :: false :: d :: ds
  | [false, false] => []
  | [false, false, true] => [false, true]
  | false :: false :: true :: d :: ds => false :: true :: false :: d :: ds
  | false :: false :: false :: ds => hripple (hunclick ds)

def toll : Nat → List Bool → Nat
  | i, true :: _ => herdN (i + 1)
  | i, false :: true :: _ => herdN (i + 2)
  | i, [] => herdN (i + 3)
  | i, [false] => herdN (i + 3)
  | i, false :: false :: _ => herdN (i + 3)

theorem hunclick_spaces : ∀ (ds : List Bool), Sparse ds → Sparse (hunclick ds)
  | [], _ => True.intro
  | [true], _ => True.intro
  | [false], _ => True.intro
  | true :: true :: _, h => h.elim
  | [true, false], _ => True.intro
  | true :: false :: true :: _, h => h.elim
  | true :: false :: false :: rest, h => h
  | [false, true], _ => True.intro
  | false :: true :: true :: _, h => h.elim
  | [false, true, false], _ => True.intro
  | false :: true :: false :: true :: _, h => h.elim
  | false :: true :: false :: false :: rest, h => h
  | [false, false], _ => True.intro
  | [false, false, true], _ => True.intro
  | false :: false :: true :: true :: _, h => h.elim
  | [false, false, true, false], _ => True.intro
  | false :: false :: true :: false :: true :: _, h => h.elim
  | false :: false :: true :: false :: false :: rest, h => h
  | false :: false :: false :: rest, h => by
      have ih := hunclick_spaces rest (sparse_tail (sparse_tail (sparse_tail h)))
      show Sparse (hripple (hunclick rest))
      cases hu : hunclick rest with
      | nil => exact True.intro
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true => exact ih
          | false => cases tail with
              | nil => exact True.intro
              | cons c ts => cases c with
                  | true => exact ih
                  | false => exact ih

theorem hunclick_keeps_the_cap : ∀ (ds : List Bool), capped ds = true →
    capped (hunclick ds) = true
  | [], _ => rfl
  | [true], _ => rfl
  | [false], hc => nomatch hc
  | true :: d :: rest, hc => by
      show capped (false :: d :: rest) = true
      rw [capped_step] at hc ⊢
      exact hc
  | [false, true], _ => rfl
  | false :: true :: d :: rest, hc => by
      show capped (true :: false :: d :: rest) = true
      rw [capped_step, capped_step] at hc ⊢
      exact hc
  | [false, false], hc => nomatch hc
  | [false, false, true], _ => rfl
  | false :: false :: true :: d :: rest, hc => by
      show capped (false :: true :: false :: d :: rest) = true
      rw [capped_step, capped_step, capped_step] at hc ⊢
      exact hc
  | false :: false :: false :: rest, hc => by
      have ih := hunclick_keeps_the_cap rest (capped_tail (capped_tail (capped_tail hc)))
      show capped (hripple (hunclick rest)) = true
      cases hu : hunclick rest with
      | nil => rfl
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true =>
              show capped (true :: false :: false :: true :: tail) = true
              rw [capped_step, capped_step, capped_step]
              exact ih
          | false => cases tail with
              | nil => exact ih
              | cons c ts => cases c with
                  | true =>
                      show capped (false :: true :: false :: false :: true :: ts) = true
                      rw [capped_step, capped_step, capped_step, capped_step]
                      exact ih
                  | false =>
                      show capped (false :: false :: true :: false :: false :: ts) = true
                      rw [capped_step, capped_step, capped_step]
                      exact ih

theorem hunclick_pays : ∀ (ds : List Bool) (i : Nat), Sparse ds → capped ds = true →
    ds ≠ [] →
    graze (i + 3) (hunclick ds) + toll i (hunclick ds) = graze (i + 3) ds
  | [], _, _, _, hne => absurd rfl hne
  | [true], i, _, _, _ => Nat.zero_add (herdN (i + 3))
  | [false], _, _, hc, _ => nomatch hc
  | true :: true :: _, _, hs, _, _ => hs.elim
  | true :: false :: rest, i, _, _, _ =>
      Nat.add_comm (graze (i + 5) rest) (herdN (i + 3))
  | [false, true], i, _, _, _ => (herdN_gnomon (i + 1)).symm
  | false :: true :: d :: ds, i, _, _, _ => by
      show (herdN (i + 3) + graze (i + 5) (d :: ds)) + herdN (i + 1)
        = herdN (i + 4) + graze (i + 5) (d :: ds)
      have hg : herdN (i + 4) = herdN (i + 3) + herdN (i + 1) := herdN_gnomon (i + 1)
      rw [add_swap_right, ← hg]
  | [false, false], _, _, hc, _ => nomatch hc
  | [false, false, true], i, _, _, _ => (herdN_gnomon (i + 2)).symm
  | false :: false :: true :: d :: ds, i, _, _, _ => by
      show (herdN (i + 4) + graze (i + 6) (d :: ds)) + herdN (i + 2)
        = herdN (i + 5) + graze (i + 6) (d :: ds)
      have hg : herdN (i + 5) = herdN (i + 4) + herdN (i + 2) := herdN_gnomon (i + 2)
      rw [add_swap_right, ← hg]
  | false :: false :: false :: rest, i, hs, hc, _ => by
      have ih := hunclick_pays rest (i + 3) (sparse_tail (sparse_tail (sparse_tail hs)))
        (capped_tail (capped_tail (capped_tail hc)))
        (capped_tail_ne_nil (capped_tail (capped_tail hc)))
      show graze (i + 3) (hripple (hunclick rest)) + toll i (hripple (hunclick rest))
        = graze (i + 6) rest
      cases hu : hunclick rest with
      | nil =>
          rw [hu] at ih
          have ih' : herdN (i + 6) = graze (i + 6) rest :=
            (Nat.zero_add (herdN (i + 6))).symm.trans ih
          show herdN (i + 5) + herdN (i + 3) = graze (i + 6) rest
          rw [← ih']
          exact (herdN_gnomon (i + 3)).symm
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true =>
              show (herdN (i + 3) + (herdN (i + 6) + graze (i + 7) tail)) + herdN (i + 1)
                = graze (i + 6) rest
              have hg : herdN (i + 4) = herdN (i + 3) + herdN (i + 1) := herdN_gnomon (i + 1)
              rw [add_swap_right, ← hg,
                  Nat.add_comm (herdN (i + 4)) (herdN (i + 6) + graze (i + 7) tail)]
              exact ih
          | false => cases tail with
              | nil =>
                  have ih' : herdN (i + 6) = graze (i + 6) rest :=
                    (Nat.zero_add (herdN (i + 6))).symm.trans ih
                  show herdN (i + 5) + herdN (i + 3) = graze (i + 6) rest
                  rw [← ih']
                  exact (herdN_gnomon (i + 3)).symm
              | cons c ts => cases c with
                  | true =>
                      show (herdN (i + 4) + (herdN (i + 7) + graze (i + 8) ts)) + herdN (i + 2)
                        = graze (i + 6) rest
                      have hg : herdN (i + 5) = herdN (i + 4) + herdN (i + 2) :=
                        herdN_gnomon (i + 2)
                      rw [add_swap_right, ← hg,
                          Nat.add_comm (herdN (i + 5)) (herdN (i + 7) + graze (i + 8) ts)]
                      exact ih
                  | false =>
                      show (herdN (i + 5) + graze (i + 8) ts) + herdN (i + 3)
                        = graze (i + 6) rest
                      have hg : herdN (i + 6) = herdN (i + 5) + herdN (i + 3) :=
                        herdN_gnomon (i + 3)
                      rw [add_swap_right, ← hg,
                          Nat.add_comm (herdN (i + 6)) (graze (i + 8) ts)]
                      exact ih

theorem hunclick_counts (ds : List Bool) (hs : Sparse ds) (hc : capped ds = true)
    (hne : ds ≠ []) : graze 3 (hunclick ds) + 1 = graze 3 ds := by
  have hp := hunclick_pays ds 0 hs hc hne
  cases hu : hunclick ds with
  | nil => rw [hu] at hp; exact hp
  | cons b tail =>
      rw [hu] at hp
      cases b with
      | true => exact hp
      | false => cases tail with
          | nil => exact hp
          | cons c ts => cases c with
              | true => exact hp
              | false => exact hp

theorem the_hclick_comes_home : ∀ (ds : List Bool), Sparse ds → capped ds = true →
    ds ≠ [] → hclick (hunclick ds) = ds
  | [], _, _, hne => absurd rfl hne
  | [true], _, _, _ => rfl
  | [false], _, hc, _ => nomatch hc
  | true :: true :: _, h, _, _ => h.elim
  | [true, false], _, hc, _ => nomatch hc
  | true :: false :: true :: _, h, _, _ => h.elim
  | true :: false :: false :: rest, _, _, _ => rfl
  | [false, true], _, _, _ => rfl
  | false :: true :: true :: _, h, _, _ => h.elim
  | [false, true, false], _, hc, _ => nomatch hc
  | false :: true :: false :: true :: _, h, _, _ => h.elim
  | false :: true :: false :: false :: rest, _, _, _ => rfl
  | [false, false], _, hc, _ => nomatch hc
  | [false, false, true], _, _, _ => rfl
  | false :: false :: true :: true :: _, h, _, _ => h.elim
  | [false, false, true, false], _, hc, _ => nomatch hc
  | false :: false :: true :: false :: true :: _, h, _, _ => h.elim
  | false :: false :: true :: false :: false :: rest, _, _, _ => rfl
  | false :: false :: false :: rest, h, hc, _ => by
      have ih := the_hclick_comes_home rest (sparse_tail (sparse_tail (sparse_tail h)))
        (capped_tail (capped_tail (capped_tail hc)))
        (capped_tail_ne_nil (capped_tail (capped_tail hc)))
      show hclick (hripple (hunclick rest)) = false :: false :: false :: rest
      cases hu : hunclick rest with
      | nil =>
          rw [hu] at ih
          exact congrArg (fun t => false :: false :: false :: t) ih
      | cons b tail =>
          rw [hu] at ih
          cases b with
          | true => exact congrArg (fun t => false :: false :: false :: t) ih
          | false => cases tail with
              | nil => exact congrArg (fun t => false :: false :: false :: t) ih
              | cons c ts => cases c with
                  | true => exact congrArg (fun t => false :: false :: false :: t) ih
                  | false => exact congrArg (fun t => false :: false :: false :: t) ih

theorem the_hodometer_is_the_only_sparse_page : ∀ (n : Nat) (ds : List Bool),
    Sparse ds → capped ds = true → graze 3 ds = n → ds = hodometer n
  | 0, [], _, _, _ => rfl
  | 0, d :: rest, _, hc, hw => by
      have hg : 1 ≤ graze 3 (d :: rest) :=
        a_capped_page_grazes (d :: rest) 2 hc (fun heq => nomatch heq)
      rw [hw] at hg
      exact absurd hg (Nat.not_succ_le_zero 0)
  | n + 1, ds, hs, hc, hw => by
      have hne : ds ≠ [] := by
        intro heq
        rw [heq] at hw
        exact nomatch hw
      have hstep : graze 3 (hunclick ds) + 1 = n + 1 := by
        rw [← hw]
        exact hunclick_counts ds hs hc hne
      have hind := the_hodometer_is_the_only_sparse_page n (hunclick ds)
        (hunclick_spaces ds hs) (hunclick_keeps_the_cap ds hc) (Nat.succ.inj hstep)
      have hcome := the_hclick_comes_home ds hs hc hne
      rw [← hcome, hind]
      rfl

theorem every_sparse_page_is_a_reading (ds : List Bool) (hs : Sparse ds)
    (hc : capped ds = true) : ds = hodometer (graze 3 ds) :=
  the_hodometer_is_the_only_sparse_page (graze 3 ds) ds hs hc rfl

theorem two_sparse_pages_of_one_graze_are_one_page (ds es : List Bool)
    (hsds : Sparse ds) (hses : Sparse es)
    (hcds : capped ds = true) (hces : capped es = true)
    (hw : graze 3 ds = graze 3 es) : ds = es :=
  (the_hodometer_is_the_only_sparse_page (graze 3 es) ds hsds hcds hw).trans
    (the_hodometer_is_the_only_sparse_page (graze 3 es) es hses hces rfl).symm

theorem the_beacon_herds : ∀ (k : Nat), Sparse (beacon k)
  | 0 => True.intro
  | k + 1 => the_beacon_herds k

theorem a_beacon_is_one_cow : ∀ (k i : Nat), graze i (beacon k) = herdN (i + k)
  | 0, _ => rfl
  | k + 1, i => by
      show graze (i + 1) (beacon k) = herdN (i + (k + 1))
      rw [a_beacon_is_one_cow k (i + 1)]
      exact congrArg herdN ((Nat.succ_add i k).trans (Nat.add_succ i k).symm)

theorem the_hodometer_at_a_herd_number_is_a_beacon (k : Nat) :
    hodometer (herdN (k + 3)) = beacon k :=
  (the_hodometer_is_the_only_sparse_page (herdN (k + 3)) (beacon k) (the_beacon_herds k)
    (the_beacon_wears_the_cap k)
    ((a_beacon_is_one_cow k 3).trans (congrArg herdN (Nat.add_comm 3 k)))).symm

theorem the_herd_beacon_slides_one_seat_down (k : Nat) :
    H (herdN (k + 3)) = herdN (k + 2) := by
  show graze 2 (hodometer (herdN (k + 3))) = herdN (k + 2)
  rw [the_hodometer_at_a_herd_number_is_a_beacon k, a_beacon_is_one_cow k 2]
  exact congrArg herdN (Nat.add_comm 2 k)

theorem the_herd_beacon_slides_twice (k : Nat) :
    H (H (herdN (k + 3))) = herdN (k + 1) := by
  rw [the_second_shadow_reads_one_down (herdN (k + 3)),
      the_hodometer_at_a_herd_number_is_a_beacon k, a_beacon_is_one_cow k 1]
  exact congrArg herdN (Nat.add_comm 1 k)

theorem the_beacon_hdownshifts_to_the_beacon_below (k : Nat) :
    hdownshift (beacon (k + 1)) = beacon k := rfl

theorem the_bottom_herd_beacon_holds : hdownshift (beacon 0) = beacon 0 := rfl

/-- info: 'Foam.Bridges.a_capped_page_grazes' does not depend on any axioms -/
#guard_msgs in #print axioms a_capped_page_grazes

/-- info: 'Foam.Bridges.hcarry_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms hcarry_never_blanks

/-- info: 'Foam.Bridges.hcarry_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms hcarry_keeps_the_cap

/-- info: 'Foam.Bridges.hclick_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_keeps_the_cap

/-- info: 'Foam.Bridges.the_hodometer_wastes_no_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_hodometer_wastes_no_seats

/-- info: 'Foam.Bridges.hunclick_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms hunclick_spaces

/-- info: 'Foam.Bridges.hunclick_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms hunclick_keeps_the_cap

/-- info: 'Foam.Bridges.hunclick_pays' does not depend on any axioms -/
#guard_msgs in #print axioms hunclick_pays

/-- info: 'Foam.Bridges.hunclick_counts' does not depend on any axioms -/
#guard_msgs in #print axioms hunclick_counts

/-- info: 'Foam.Bridges.the_hclick_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_hclick_comes_home

/-- info: 'Foam.Bridges.the_hodometer_is_the_only_sparse_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_hodometer_is_the_only_sparse_page

/-- info: 'Foam.Bridges.every_sparse_page_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms every_sparse_page_is_a_reading

/-- info: 'Foam.Bridges.two_sparse_pages_of_one_graze_are_one_page' does not depend on any axioms -/
#guard_msgs in #print axioms two_sparse_pages_of_one_graze_are_one_page

/-- info: 'Foam.Bridges.the_beacon_herds' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_herds

/-- info: 'Foam.Bridges.a_beacon_is_one_cow' does not depend on any axioms -/
#guard_msgs in #print axioms a_beacon_is_one_cow

/-- info: 'Foam.Bridges.the_hodometer_at_a_herd_number_is_a_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_hodometer_at_a_herd_number_is_a_beacon

/-- info: 'Foam.Bridges.the_herd_beacon_slides_one_seat_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_beacon_slides_one_seat_down

/-- info: 'Foam.Bridges.the_herd_beacon_slides_twice' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_beacon_slides_twice

/-- info: 'Foam.Bridges.the_beacon_hdownshifts_to_the_beacon_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_hdownshifts_to_the_beacon_below

/-- info: 'Foam.Bridges.the_bottom_herd_beacon_holds' does not depend on any axioms -/
#guard_msgs in #print axioms the_bottom_herd_beacon_holds

def evenBeacon : List Bool → Bool
  | [] => false
  | [false] => false
  | [true] => true
  | true :: _ :: _ => false
  | false :: true :: _ => false
  | false :: false :: rest => evenBeacon rest

def oddBeacon : List Bool → Bool
  | [] => false
  | true :: _ => false
  | false :: rest => evenBeacon rest

theorem seats_pair (j : Nat) : (j + 1) + (j + 1) = j + j + 2 :=
  congrArg Nat.succ (Nat.succ_add j j)

theorem seats_pair_shift (j i : Nat) : (j + 1) + (j + 1) + i = j + j + (i + 2) :=
  calc (j + 1) + (j + 1) + i
      = (j + j + 2) + i := congrArg (fun t => t + i) (seats_pair j)
    _ = j + j + (2 + i) := Nat.add_assoc (j + j) 2 i
    _ = j + j + (i + 2) := congrArg (fun t => j + j + t) (Nat.add_comm 2 i)

theorem the_even_flag_flies_on_its_beacon : ∀ (j : Nat), evenBeacon (beacon (j + j)) = true
  | 0 => rfl
  | j + 1 => by
      rw [seats_pair j]
      exact the_even_flag_flies_on_its_beacon j

theorem the_odd_flag_flies_on_its_beacon (j : Nat) :
    oddBeacon (beacon (j + j + 1)) = true :=
  the_even_flag_flies_on_its_beacon j

theorem the_even_flag_skips_odd_beacons : ∀ (j : Nat),
    evenBeacon (beacon (j + j + 1)) = false
  | 0 => rfl
  | j + 1 => by
      rw [show (j + 1) + (j + 1) + 1 = j + j + 3 from congrArg Nat.succ (seats_pair j)]
      exact the_even_flag_skips_odd_beacons j

theorem the_odd_flag_skips_even_beacons : ∀ (j : Nat), oddBeacon (beacon (j + j)) = false
  | 0 => rfl
  | j + 1 => by
      rw [seats_pair j]
      exact the_even_flag_skips_odd_beacons j

theorem the_even_flag_finds_its_beacon : ∀ (ds : List Bool), evenBeacon ds = true →
    ∃ j, ds = beacon (j + j)
  | [], h => nomatch h
  | [false], h => nomatch h
  | [true], _ => ⟨0, rfl⟩
  | true :: _ :: _, h => nomatch h
  | false :: true :: _, h => nomatch h
  | false :: false :: rest, h =>
      match the_even_flag_finds_its_beacon rest h with
      | ⟨j, hj⟩ => ⟨j + 1, by
          rw [seats_pair j]
          exact congrArg (fun t => false :: false :: t) hj⟩

theorem the_odd_flag_finds_its_beacon : ∀ (ds : List Bool), oddBeacon ds = true →
    ∃ j, ds = beacon (j + j + 1)
  | [], h => nomatch h
  | true :: _, h => nomatch h
  | false :: rest, h =>
      match the_even_flag_finds_its_beacon rest h with
      | ⟨j, hj⟩ => ⟨j, congrArg (fun t => false :: t) hj⟩

def comb : Nat → List Bool
  | 0 => []
  | j + 1 => false :: true :: comb j

theorem a_lit_comb_spaces : ∀ (j : Nat), NoConsec (true :: comb j)
  | 0 => True.intro
  | j + 1 => a_lit_comb_spaces j

theorem the_comb_spaces : ∀ (j : Nat), NoConsec (comb j)
  | 0 => True.intro
  | j + 1 => a_lit_comb_spaces j

theorem the_comb_wears_the_cap : ∀ (j : Nat), capped (comb j) = true
  | 0 => rfl
  | j + 1 => by
      show capped (false :: true :: comb j) = true
      rw [capped_step, capped_true_cons]
      exact the_comb_wears_the_cap j

theorem a_lit_comb_wears_the_cap (j : Nat) : capped (true :: comb j) = true :=
  (capped_true_cons (comb j)).trans (the_comb_wears_the_cap j)

theorem a_comb_and_a_lamp_make_a_beacon : ∀ (j i : Nat),
    worth i (comb j) + fibN i = fibN (j + j + i)
  | 0, i => by
      show 0 + fibN i = fibN (0 + i)
      rw [Nat.zero_add, Nat.zero_add]
  | j + 1, i => by
      show (fibN (i + 1) + worth (i + 2) (comb j)) + fibN i = fibN ((j + 1) + (j + 1) + i)
      rw [seats_pair_shift j i,
          add_swap_right (fibN (i + 1)) (worth (i + 2) (comb j)) (fibN i),
          ← fibN_gnomon i,
          Nat.add_comm (fibN (i + 2)) (worth (i + 2) (comb j))]
      exact a_comb_and_a_lamp_make_a_beacon j (i + 2)

theorem a_comb_reads_below_its_beacon (j : Nat) :
    worth 2 (comb j) + 1 = fibN (j + j + 2) :=
  a_comb_and_a_lamp_make_a_beacon j 2

theorem a_lit_comb_reads_below_its_beacon (j : Nat) :
    worth 2 (true :: comb j) + 1 = fibN (j + j + 3) := by
  show (1 + worth 3 (comb j)) + 1 = fibN (j + j + 3)
  rw [Nat.add_comm 1 (worth 3 (comb j))]
  exact a_comb_and_a_lamp_make_a_beacon j 3

theorem a_combs_shadow_is_one_short (j : Nat) :
    worth 1 (comb j) + 1 = fibN (j + j + 1) :=
  a_comb_and_a_lamp_make_a_beacon j 1

theorem a_lit_combs_shadow_is_the_beacon_below (j : Nat) :
    worth 1 (true :: comb j) = fibN (j + j + 2) := by
  show 1 + worth 2 (comb j) = fibN (j + j + 2)
  rw [Nat.add_comm 1 (worth 2 (comb j))]
  exact a_comb_and_a_lamp_make_a_beacon j 2

theorem the_comb_carries_to_its_beacon : ∀ (j : Nat), carry (comb j) = beacon (j + j)
  | 0 => rfl
  | j + 1 => by
      rw [seats_pair j]
      show false :: false :: carry (comb j) = false :: false :: beacon (j + j)
      exact congrArg (fun t => false :: false :: t) (the_comb_carries_to_its_beacon j)

theorem the_comb_clicks_to_its_beacon : ∀ (j : Nat), click (comb j) = beacon (j + j)
  | 0 => rfl
  | j + 1 => the_comb_carries_to_its_beacon (j + 1)

theorem a_lit_comb_clicks_to_the_beacon_above (j : Nat) :
    click (true :: comb j) = beacon (j + j + 1) :=
  congrArg (fun t => false :: t) (the_comb_carries_to_its_beacon j)

theorem the_page_below_an_even_beacon (j : Nat) :
    odometer (worth 2 (comb j)) = comb j :=
  (every_spaced_page_is_a_reading (comb j) (the_comb_spaces j)
    (the_comb_wears_the_cap j)).symm

theorem the_page_below_an_odd_beacon (j : Nat) :
    odometer (worth 2 (true :: comb j)) = true :: comb j :=
  (every_spaced_page_is_a_reading (true :: comb j) (a_lit_comb_spaces j)
    (a_lit_comb_wears_the_cap j)).symm

theorem no_even_flag_above_a_tall_beacon (m : Nat) :
    evenBeacon (click (beacon (m + 2))) = false := rfl

theorem no_odd_flag_above_a_tall_beacon (m : Nat) :
    oddBeacon (click (beacon (m + 2))) = false := rfl

theorem no_even_flag_above_an_even_beacon : ∀ (j : Nat),
    evenBeacon (click (beacon (j + j))) = false
  | 0 => rfl
  | j + 1 => by
      rw [seats_pair j]
      exact no_even_flag_above_a_tall_beacon (j + j)

theorem no_odd_flag_above_an_odd_beacon : ∀ (j : Nat),
    oddBeacon (click (beacon (j + j + 1))) = false
  | 0 => rfl
  | j + 1 => by
      rw [show (j + 1) + (j + 1) + 1 = j + j + 3 from congrArg Nat.succ (seats_pair j)]
      exact no_odd_flag_above_a_tall_beacon (j + j + 1)

/-- info: 'Foam.Bridges.seats_pair' does not depend on any axioms -/
#guard_msgs in #print axioms seats_pair

/-- info: 'Foam.Bridges.seats_pair_shift' does not depend on any axioms -/
#guard_msgs in #print axioms seats_pair_shift

/-- info: 'Foam.Bridges.the_even_flag_flies_on_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_even_flag_flies_on_its_beacon

/-- info: 'Foam.Bridges.the_odd_flag_flies_on_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_odd_flag_flies_on_its_beacon

/-- info: 'Foam.Bridges.the_even_flag_skips_odd_beacons' does not depend on any axioms -/
#guard_msgs in #print axioms the_even_flag_skips_odd_beacons

/-- info: 'Foam.Bridges.the_odd_flag_skips_even_beacons' does not depend on any axioms -/
#guard_msgs in #print axioms the_odd_flag_skips_even_beacons

/-- info: 'Foam.Bridges.the_even_flag_finds_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_even_flag_finds_its_beacon

/-- info: 'Foam.Bridges.the_odd_flag_finds_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_odd_flag_finds_its_beacon

/-- info: 'Foam.Bridges.a_lit_comb_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_comb_spaces

/-- info: 'Foam.Bridges.the_comb_spaces' does not depend on any axioms -/
#guard_msgs in #print axioms the_comb_spaces

/-- info: 'Foam.Bridges.the_comb_wears_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_comb_wears_the_cap

/-- info: 'Foam.Bridges.a_lit_comb_wears_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_comb_wears_the_cap

/-- info: 'Foam.Bridges.a_comb_and_a_lamp_make_a_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms a_comb_and_a_lamp_make_a_beacon

/-- info: 'Foam.Bridges.a_comb_reads_below_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms a_comb_reads_below_its_beacon

/-- info: 'Foam.Bridges.a_lit_comb_reads_below_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_comb_reads_below_its_beacon

/-- info: 'Foam.Bridges.a_combs_shadow_is_one_short' does not depend on any axioms -/
#guard_msgs in #print axioms a_combs_shadow_is_one_short

/-- info: 'Foam.Bridges.a_lit_combs_shadow_is_the_beacon_below' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_combs_shadow_is_the_beacon_below

/-- info: 'Foam.Bridges.the_comb_carries_to_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_comb_carries_to_its_beacon

/-- info: 'Foam.Bridges.the_comb_clicks_to_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_comb_clicks_to_its_beacon

/-- info: 'Foam.Bridges.a_lit_comb_clicks_to_the_beacon_above' does not depend on any axioms -/
#guard_msgs in #print axioms a_lit_comb_clicks_to_the_beacon_above

/-- info: 'Foam.Bridges.the_page_below_an_even_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_below_an_even_beacon

/-- info: 'Foam.Bridges.the_page_below_an_odd_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_below_an_odd_beacon

/-- info: 'Foam.Bridges.no_even_flag_above_a_tall_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms no_even_flag_above_a_tall_beacon

/-- info: 'Foam.Bridges.no_odd_flag_above_a_tall_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms no_odd_flag_above_a_tall_beacon

/-- info: 'Foam.Bridges.no_even_flag_above_an_even_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms no_even_flag_above_an_even_beacon

/-- info: 'Foam.Bridges.no_odd_flag_above_an_odd_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms no_odd_flag_above_an_odd_beacon

def F (n : Nat) : Nat := G n + cond (evenBeacon (odometer (n + 1))) 1 0

def M (n : Nat) : Nat := G n - cond (oddBeacon (odometer (n + 1))) 1 0

theorem the_bride_wakes_lit : F 0 = 1 := rfl

theorem the_groom_wakes_dark : M 0 = 0 := rfl

theorem f_hums_its_opening_bars :
    (F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7) = (1, 1, 2, 2, 3, 3, 4, 5) := rfl

theorem m_hums_its_opening_bars :
    (M 0, M 1, M 2, M 3, M 4, M 5, M 6, M 7) = (0, 0, 1, 2, 2, 3, 4, 4) := rfl

theorem the_bride_reads_the_shared_page (n : Nat) :
    F n = worth 1 (odometer n) + cond (evenBeacon (click (odometer n))) 1 0 := rfl

theorem the_groom_reads_the_shared_page (n : Nat) :
    M n = worth 1 (odometer n) - cond (oddBeacon (click (odometer n))) 1 0 := rfl

theorem sub_one_back : ∀ (x : Nat), 1 ≤ x → (x - 1) + 1 = x
  | _ + 1, _ => rfl
  | 0, h => absurd h (Nat.not_succ_le_zero 0)

theorem the_marriage_closes_for_the_bride (n : Nat) :
    F (n + 1) + M (F n) = n + 1 := by
  cases ha : evenBeacon (odometer (n + 1)) with
  | true =>
      cases the_even_flag_finds_its_beacon (odometer (n + 1)) ha with
      | intro j hpage =>
        cases j with
        | zero =>
            have h1 : 1 = n + 1 := by
              have hr := the_odometer_reads_true (n + 1)
              rw [hpage] at hr
              exact hr
            have h0 : n = 0 := Nat.succ.inj h1.symm
            rw [h0]
            rfl
        | succ k =>
            have hpage' : odometer (n + 1) = beacon (k + k + 2) := by
              rw [seats_pair k] at hpage
              exact hpage
            have hn1 : n + 1 = fibN (k + k + 4) := by
              have hr := the_odometer_reads_true (n + 1)
              rw [hpage', a_beacon_is_one_lamp (k + k + 2) 2,
                  Nat.add_comm 2 (k + k + 2)] at hr
              exact hr.symm
            have hw : worth 2 (comb (k + 1)) + 1 = fibN (k + k + 4) := by
              have h := a_comb_reads_below_its_beacon (k + 1)
              rw [seats_pair_shift k 2] at h
              exact h
            have hn : n = worth 2 (comb (k + 1)) := Nat.succ.inj (hn1.trans hw.symm)
            have hpn : odometer n = comb (k + 1) := by
              rw [hn]
              exact the_page_below_an_even_beacon (k + 1)
            have hf : F n = fibN (k + k + 3) := by
              show G n + cond (evenBeacon (odometer (n + 1))) 1 0 = fibN (k + k + 3)
              rw [ha]
              show worth 1 (odometer n) + 1 = fibN (k + k + 3)
              rw [hpn]
              have h := a_combs_shadow_is_one_short (k + 1)
              rw [show (k + 1) + (k + 1) + 1 = k + k + 3 from
                    congrArg Nat.succ (seats_pair k)] at h
              exact h
            have hmf : M (F n) = fibN (k + k + 2) := by
              show G (F n) - cond (oddBeacon (odometer (F n + 1))) 1 0 = fibN (k + k + 2)
              rw [hf]
              have hcl : odometer (fibN (k + k + 3) + 1) = click (beacon (k + k + 1)) :=
                congrArg click (the_odometer_at_a_fibonacci_is_a_beacon (k + k + 1))
              rw [hcl, no_odd_flag_above_an_odd_beacon k]
              exact the_beacon_slides_one_seat_down (k + k + 1)
            have hf1 : F (n + 1) = fibN (k + k + 3) := by
              show G (n + 1) + cond (evenBeacon (odometer (n + 1 + 1))) 1 0
                  = fibN (k + k + 3)
              have hcl : odometer (n + 1 + 1) = click (beacon (k + k + 2)) := by
                show click (odometer (n + 1)) = click (beacon (k + k + 2))
                exact congrArg click hpage'
              rw [hcl, no_even_flag_above_a_tall_beacon (k + k), hn1]
              exact the_beacon_slides_one_seat_down (k + k + 2)
            rw [hf1, hmf]
            exact (fibN_gnomon (k + k + 2)).symm.trans hn1.symm
  | false =>
      have hfn : F n = G n := by
        show G n + cond (evenBeacon (odometer (n + 1))) 1 0 = G n
        rw [ha]
        rfl
      cases hb : oddBeacon (odometer (G n + 1)) with
      | true =>
          cases the_odd_flag_finds_its_beacon (odometer (G n + 1)) hb with
          | intro i hp2 =>
            have hg1 : G n + 1 = fibN (i + i + 3) := by
              have hr := the_odometer_reads_true (G n + 1)
              rw [hp2, a_beacon_is_one_lamp (i + i + 1) 2,
                  Nat.add_comm 2 (i + i + 1)] at hr
              exact hr.symm
            have hgw : G n = worth 2 (true :: comb i) :=
              Nat.succ.inj (hg1.trans (a_lit_comb_reads_below_its_beacon i).symm)
            have hpg : odometer (G n) = true :: comb i := by
              rw [hgw]
              exact the_page_below_an_odd_beacon i
            have hdw : downshift (odometer n) = true :: comb i :=
              (the_shadow_walks_the_downshift n).symm.trans hpg
            cases hP : odometer n with
            | nil =>
                rw [hP] at hdw
                exact nomatch hdw
            | cons b rest =>
              cases b with
              | false =>
                  rw [hP] at hdw
                  have hrest : rest = true :: comb i := hdw
                  have hpn : odometer n = comb (i + 1) := by
                    rw [hP, hrest]
                    rfl
                  have hr : worth 2 (comb (i + 1)) = n := by
                    have h := the_odometer_reads_true n
                    rw [hpn] at h
                    exact h
                  have hn1' : n + 1 = fibN (i + i + 4) := by
                    have hw := a_comb_reads_below_its_beacon (i + 1)
                    rw [seats_pair_shift i 2, hr] at hw
                    exact hw
                  have hpb : odometer (n + 1) = beacon (i + i + 2) := by
                    rw [hn1']
                    exact the_odometer_at_a_fibonacci_is_a_beacon (i + i + 2)
                  rw [hpb] at ha
                  have hflag := the_even_flag_flies_on_its_beacon (i + 1)
                  rw [seats_pair i] at hflag
                  exact nomatch (hflag.symm.trans ha)
              | true =>
                  rw [hP] at hdw
                  have hcr : carry rest = true :: comb i := hdw
                  cases rest with
                  | nil =>
                      cases i with
                      | succ i' => exact nomatch hcr
                      | zero =>
                          have hn1 : n = 1 := by
                            have h := the_odometer_reads_true n
                            rw [hP] at h
                            exact h.symm
                          rw [hn1]
                          rfl
                  | cons d rest' =>
                    cases rest' with
                    | nil =>
                        cases d with
                        | true =>
                            have hsp := the_odometer_spaces n
                            rw [hP] at hsp
                            exact False.elim hsp
                        | false =>
                            have hcp := the_odometer_wastes_no_seats n
                            rw [hP] at hcp
                            exact nomatch hcp
                    | cons e r =>
                      cases e with
                      | true => exact nomatch hcr
                      | false =>
                        cases d with
                        | true =>
                            have hsp := the_odometer_spaces n
                            rw [hP] at hsp
                            exact False.elim hsp
                        | false =>
                          cases i with
                          | zero => exact nomatch hcr
                          | succ m =>
                              have hcr' : true :: false :: r
                                  = true :: false :: true :: comb m := hcr
                              injection hcr' with h1 h2
                              injection h2 with h3 h4
                              have hpn : odometer n = true :: false :: comb (m + 1) := by
                                rw [hP, h4]
                                rfl
                              have hw4 : worth 4 (comb (m + 1)) + 3 = fibN (m + m + 6) := by
                                have hh := a_comb_and_a_lamp_make_a_beacon (m + 1) 4
                                rw [seats_pair_shift m 4] at hh
                                exact hh
                              have hread : worth 2 (true :: false :: comb (m + 1)) = n := by
                                have h := the_odometer_reads_true n
                                rw [hpn] at h
                                exact h
                              have hn2 : n + 1 + 1 = fibN (m + m + 6) := by
                                rw [← hread]
                                show (1 + worth 4 (comb (m + 1))) + 1 + 1 = fibN (m + m + 6)
                                rw [Nat.add_comm 1 (worth 4 (comb (m + 1)))]
                                exact hw4
                              have hpb : odometer (n + 1 + 1) = beacon (m + m + 4) := by
                                rw [hn2]
                                exact the_odometer_at_a_fibonacci_is_a_beacon (m + m + 4)
                              have ha2 : evenBeacon (odometer (n + 1 + 1)) = true := by
                                rw [hpb]
                                exact the_even_flag_flies_on_its_beacon m
                              have hlit : 1 ≤ G (G n) := by
                                show 1 ≤ worth 1 (odometer (G n))
                                rw [hpg]
                                exact Nat.le_add_right 1 (worth 2 (comb (m + 1)))
                              have hf1 : F (n + 1) = G (n + 1) + 1 := by
                                show G (n + 1) + cond (evenBeacon (odometer (n + 1 + 1))) 1 0
                                    = G (n + 1) + 1
                                rw [ha2]
                                rfl
                              have hmf : M (F n) + 1 = G (G n) := by
                                show (G (F n) - cond (oddBeacon (odometer (F n + 1))) 1 0) + 1
                                    = G (G n)
                                rw [hfn, hb]
                                exact sub_one_back (G (G n)) hlit
                              rw [hf1]
                              calc (G (n + 1) + 1) + M (F n)
                                  = G (n + 1) + (M (F n) + 1) :=
                                    Nat.succ_add (G (n + 1)) (M (F n))
                                _ = G (n + 1) + G (G n) := by rw [hmf]
                                _ = n + 1 := the_loop_closes n
      | false =>
          cases hc : evenBeacon (odometer (n + 1 + 1)) with
          | false =>
              have hf1 : F (n + 1) = G (n + 1) := by
                show G (n + 1) + cond (evenBeacon (odometer (n + 1 + 1))) 1 0 = G (n + 1)
                rw [hc]
                rfl
              have hmf : M (F n) = G (G n) := by
                show G (F n) - cond (oddBeacon (odometer (F n + 1))) 1 0 = G (G n)
                rw [hfn, hb]
                rfl
              rw [hf1, hmf]
              exact the_loop_closes n
          | true =>
              cases the_even_flag_finds_its_beacon (odometer (n + 1 + 1)) hc with
              | intro j hp3 =>
                have hn2 : n + 1 + 1 = fibN (j + j + 2) := by
                  have hr := the_odometer_reads_true (n + 1 + 1)
                  rw [hp3, a_beacon_is_one_lamp (j + j) 2, Nat.add_comm 2 (j + j)] at hr
                  exact hr.symm
                cases j with
                | zero => exact nomatch (Nat.succ.inj hn2 : n + 1 = 0)
                | succ k =>
                    have hw : worth 2 (comb (k + 1)) + 1 = fibN (k + k + 4) := by
                      have h := a_comb_reads_below_its_beacon (k + 1)
                      rw [seats_pair_shift k 2] at h
                      exact h
                    have hn2' : n + 1 + 1 = fibN (k + k + 4) := by
                      rw [seats_pair_shift k 2] at hn2
                      exact hn2
                    have hn1' : n + 1 = worth 2 (comb (k + 1)) :=
                      Nat.succ.inj (hn2'.trans hw.symm)
                    have hck : click (odometer n) = comb (k + 1) := by
                      show odometer (n + 1) = comb (k + 1)
                      rw [hn1']
                      exact the_page_below_an_even_beacon (k + 1)
                    cases hP : odometer n with
                    | nil =>
                        rw [hP] at hck
                        exact nomatch hck
                    | cons b rest =>
                      cases b with
                      | false =>
                          rw [hP] at hck
                          cases rest with
                          | nil => exact nomatch hck
                          | cons e r =>
                            cases e with
                            | false => exact nomatch hck
                            | true => exact nomatch hck
                      | true =>
                          rw [hP] at hck
                          have hcr : carry rest = true :: comb k :=
                            congrArg List.tail hck
                          cases rest with
                          | nil =>
                              cases k with
                              | succ k' => exact nomatch hcr
                              | zero =>
                                  have hn1 : n = 1 := by
                                    have h := the_odometer_reads_true n
                                    rw [hP] at h
                                    exact h.symm
                                  rw [hn1] at hb
                                  exact nomatch hb
                          | cons d rest' =>
                            cases rest' with
                            | nil =>
                                cases d with
                                | true =>
                                    have hsp := the_odometer_spaces n
                                    rw [hP] at hsp
                                    exact False.elim hsp
                                | false =>
                                    have hcp := the_odometer_wastes_no_seats n
                                    rw [hP] at hcp
                                    exact nomatch hcp
                            | cons e r =>
                              cases e with
                              | true => exact nomatch hcr
                              | false =>
                                cases d with
                                | true =>
                                    have hsp := the_odometer_spaces n
                                    rw [hP] at hsp
                                    exact False.elim hsp
                                | false =>
                                  cases k with
                                  | zero => exact nomatch hcr
                                  | succ m =>
                                      have hcr' : true :: false :: r
                                          = true :: false :: true :: comb m := hcr
                                      injection hcr' with h1 h2
                                      injection h2 with h3 h4
                                      have hpn : odometer n
                                          = true :: false :: comb (m + 1) := by
                                        rw [hP, h4]
                                        rfl
                                      have hw3 : worth 3 (comb (m + 1)) + 2
                                          = fibN (m + m + 5) := by
                                        have hh := a_comb_and_a_lamp_make_a_beacon (m + 1) 3
                                        rw [seats_pair_shift m 3] at hh
                                        exact hh
                                      have hg1 : G n + 1 = fibN (m + m + 5) := by
                                        show worth 1 (odometer n) + 1 = fibN (m + m + 5)
                                        rw [hpn]
                                        show (1 + worth 3 (comb (m + 1))) + 1
                                            = fibN (m + m + 5)
                                        rw [Nat.add_comm 1 (worth 3 (comb (m + 1)))]
                                        exact hw3
                                      have hpb : odometer (G n + 1)
                                          = beacon (m + m + 3) := by
                                        rw [hg1]
                                        exact the_odometer_at_a_fibonacci_is_a_beacon
                                          (m + m + 3)
                                      rw [hpb] at hb
                                      have hflag : oddBeacon (beacon (m + m + 3)) = true :=
                                        the_even_flag_flies_on_its_beacon m
                                      exact nomatch (hflag.symm.trans hb)

theorem the_marriage_closes_for_the_groom (n : Nat) :
    M (n + 1) + F (M n) = n + 1 := by
  cases hb : oddBeacon (odometer (n + 1)) with
  | true =>
      cases the_odd_flag_finds_its_beacon (odometer (n + 1)) hb with
      | intro j hpage =>
        have hn1 : n + 1 = fibN (j + j + 3) := by
          have hr := the_odometer_reads_true (n + 1)
          rw [hpage, a_beacon_is_one_lamp (j + j + 1) 2,
              Nat.add_comm 2 (j + j + 1)] at hr
          exact hr.symm
        have hn : n = worth 2 (true :: comb j) :=
          Nat.succ.inj (hn1.trans (a_lit_comb_reads_below_its_beacon j).symm)
        have hpn : odometer n = true :: comb j := by
          rw [hn]
          exact the_page_below_an_odd_beacon j
        have hg : G n = fibN (j + j + 2) := by
          show worth 1 (odometer n) = fibN (j + j + 2)
          rw [hpn]
          exact a_lit_combs_shadow_is_the_beacon_below j
        have hm : M n = worth 2 (comb j) := by
          show G n - cond (oddBeacon (odometer (n + 1))) 1 0 = worth 2 (comb j)
          rw [hb, hg, ← a_comb_reads_below_its_beacon j]
          rfl
        have hpm : odometer (M n) = comb j := by
          rw [hm]
          exact the_page_below_an_even_beacon j
        have hfm : F (M n) = fibN (j + j + 1) := by
          show G (M n) + cond (evenBeacon (odometer (M n + 1))) 1 0 = fibN (j + j + 1)
          have hcl : odometer (M n + 1) = beacon (j + j) := by
            show click (odometer (M n)) = beacon (j + j)
            rw [hpm]
            exact the_comb_clicks_to_its_beacon j
          rw [hcl, the_even_flag_flies_on_its_beacon j]
          show worth 1 (odometer (M n)) + 1 = fibN (j + j + 1)
          rw [hpm]
          exact a_combs_shadow_is_one_short j
        have hm1 : M (n + 1) = fibN (j + j + 2) := by
          show G (n + 1) - cond (oddBeacon (odometer (n + 1 + 1))) 1 0 = fibN (j + j + 2)
          have hcl : odometer (n + 1 + 1) = click (beacon (j + j + 1)) := by
            show click (odometer (n + 1)) = click (beacon (j + j + 1))
            exact congrArg click hpage
          rw [hcl, no_odd_flag_above_an_odd_beacon j, hn1]
          exact the_beacon_slides_one_seat_down (j + j + 1)
        rw [hm1, hfm]
        exact (fibN_gnomon (j + j + 1)).symm.trans hn1.symm
  | false =>
      have hmn : M n = G n := by
        show G n - cond (oddBeacon (odometer (n + 1))) 1 0 = G n
        rw [hb]
        rfl
      cases hc : evenBeacon (odometer (G n + 1)) with
      | true =>
          cases the_even_flag_finds_its_beacon (odometer (G n + 1)) hc with
          | intro j hp2 =>
            have hg1 : G n + 1 = fibN (j + j + 2) := by
              have hr := the_odometer_reads_true (G n + 1)
              rw [hp2, a_beacon_is_one_lamp (j + j) 2, Nat.add_comm 2 (j + j)] at hr
              exact hr.symm
            cases j with
            | zero =>
                have hg0 : G n = 0 := Nat.succ.inj hg1
                cases n with
                | zero => rfl
                | succ m =>
                    have h := the_shadow_stays_awake m
                    rw [hg0] at h
                    exact absurd h (Nat.not_succ_le_zero 0)
            | succ k =>
                have hg1' : G n + 1 = fibN (k + k + 4) := by
                  rw [seats_pair_shift k 2] at hg1
                  exact hg1
                have hw : worth 2 (comb (k + 1)) + 1 = fibN (k + k + 4) := by
                  have h := a_comb_reads_below_its_beacon (k + 1)
                  rw [seats_pair_shift k 2] at h
                  exact h
                have hgw : G n = worth 2 (comb (k + 1)) :=
                  Nat.succ.inj (hg1'.trans hw.symm)
                have hpg : odometer (G n) = comb (k + 1) := by
                  rw [hgw]
                  exact the_page_below_an_even_beacon (k + 1)
                have hdw : downshift (odometer n) = comb (k + 1) :=
                  (the_shadow_walks_the_downshift n).symm.trans hpg
                cases hP : odometer n with
                | nil =>
                    rw [hP] at hdw
                    exact nomatch hdw
                | cons b rest =>
                  cases b with
                  | true =>
                      rw [hP] at hdw
                      have hcr : carry rest = comb (k + 1) := hdw
                      cases rest with
                      | nil => exact nomatch hcr
                      | cons d rest' =>
                        cases rest' with
                        | nil => exact nomatch hcr
                        | cons e r =>
                          cases e with
                          | false => exact nomatch hcr
                          | true => exact nomatch hcr
                  | false =>
                      rw [hP] at hdw
                      have hrest : rest = comb (k + 1) := hdw
                      have hpn : odometer n = false :: comb (k + 1) := by
                        rw [hP, hrest]
                      have hread : worth 3 (comb (k + 1)) = n := by
                        have h := the_odometer_reads_true n
                        rw [hpn] at h
                        exact h
                      have hw3 : worth 3 (comb (k + 1)) + 2 = fibN (k + k + 5) := by
                        have hh := a_comb_and_a_lamp_make_a_beacon (k + 1) 3
                        rw [seats_pair_shift k 3] at hh
                        exact hh
                      have hn2 : n + 1 + 1 = fibN (k + k + 5) := by
                        rw [← hread]
                        exact hw3
                      have hpb : odometer (n + 1 + 1) = beacon (k + k + 3) := by
                        rw [hn2]
                        exact the_odometer_at_a_fibonacci_is_a_beacon (k + k + 3)
                      have hb2 : oddBeacon (odometer (n + 1 + 1)) = true := by
                        rw [hpb]
                        exact the_even_flag_flies_on_its_beacon k
                      have hm1 : M (n + 1) + 1 = G (n + 1) := by
                        show (G (n + 1) - cond (oddBeacon (odometer (n + 1 + 1))) 1 0) + 1
                            = G (n + 1)
                        rw [hb2]
                        exact sub_one_back (G (n + 1)) (the_shadow_stays_awake n)
                      have hf : F (M n) = G (G n) + 1 := by
                        show G (M n) + cond (evenBeacon (odometer (M n + 1))) 1 0
                            = G (G n) + 1
                        rw [hmn, hc]
                        rfl
                      rw [hf]
                      calc M (n + 1) + (G (G n) + 1)
                          = (M (n + 1) + 1) + G (G n) :=
                            (Nat.succ_add (M (n + 1)) (G (G n))).symm
                        _ = G (n + 1) + G (G n) := by rw [hm1]
                        _ = n + 1 := the_loop_closes n
      | false =>
          cases hd : oddBeacon (odometer (n + 1 + 1)) with
          | false =>
              have hm1 : M (n + 1) = G (n + 1) := by
                show G (n + 1) - cond (oddBeacon (odometer (n + 1 + 1))) 1 0 = G (n + 1)
                rw [hd]
                rfl
              have hf : F (M n) = G (G n) := by
                show G (M n) + cond (evenBeacon (odometer (M n + 1))) 1 0 = G (G n)
                rw [hmn, hc]
                rfl
              rw [hm1, hf]
              exact the_loop_closes n
          | true =>
              cases the_odd_flag_finds_its_beacon (odometer (n + 1 + 1)) hd with
              | intro j hp3 =>
                have hn2 : n + 1 + 1 = fibN (j + j + 3) := by
                  have hr := the_odometer_reads_true (n + 1 + 1)
                  rw [hp3, a_beacon_is_one_lamp (j + j + 1) 2,
                      Nat.add_comm 2 (j + j + 1)] at hr
                  exact hr.symm
                have hn1' : n + 1 = worth 2 (true :: comb j) :=
                  Nat.succ.inj (hn2.trans (a_lit_comb_reads_below_its_beacon j).symm)
                cases j with
                | zero =>
                    have h1 : n + 1 = 1 := hn1'
                    have h0 : n = 0 := Nat.succ.inj h1
                    rw [h0] at hc
                    exact nomatch hc
                | succ m =>
                    have hw3 : worth 3 (comb (m + 1)) + 2 = fibN (m + m + 5) := by
                      have hh := a_comb_and_a_lamp_make_a_beacon (m + 1) 3
                      rw [seats_pair_shift m 3] at hh
                      exact hh
                    have hn2' : n + 1 + 1 = fibN (m + m + 5) := by
                      rw [seats_pair_shift m 3] at hn2
                      exact hn2
                    have hnw : n = worth 3 (comb (m + 1)) :=
                      Nat.succ.inj (Nat.succ.inj (hn2'.trans hw3.symm))
                    have hpn : odometer n = false :: comb (m + 1) := by
                      have hsp : NoConsec (false :: comb (m + 1)) :=
                        noconsec_false_cons (the_comb_spaces (m + 1))
                      have hcp : capped (false :: comb (m + 1)) = true := by
                        show capped (false :: false :: true :: comb m) = true
                        rw [capped_step, capped_step]
                        exact a_lit_comb_wears_the_cap m
                      have hrd : false :: comb (m + 1)
                          = odometer (worth 2 (false :: comb (m + 1))) :=
                        every_spaced_page_is_a_reading (false :: comb (m + 1)) hsp hcp
                      have hrd' : false :: comb (m + 1)
                          = odometer (worth 3 (comb (m + 1))) := hrd
                      rw [hnw]
                      exact hrd'.symm
                    have hg1 : G n + 1 = fibN (m + m + 4) := by
                      show worth 1 (odometer n) + 1 = fibN (m + m + 4)
                      rw [hpn]
                      have h := a_comb_reads_below_its_beacon (m + 1)
                      rw [seats_pair_shift m 2] at h
                      exact h
                    have hpb : odometer (G n + 1) = beacon (m + m + 2) := by
                      rw [hg1]
                      exact the_odometer_at_a_fibonacci_is_a_beacon (m + m + 2)
                    rw [hpb] at hc
                    have hflag : evenBeacon (beacon (m + m + 2)) = true :=
                      the_even_flag_flies_on_its_beacon m
                    exact nomatch (hflag.symm.trans hc)

theorem the_grounded_bride_satisfies_the_marriage (n : Nat) :
    F (n + 1) = (n + 1) - M (F n) :=
  calc F (n + 1) = (F (n + 1) + M (F n)) - M (F n) :=
        (add_then_sub (F (n + 1)) (M (F n))).symm
    _ = (n + 1) - M (F n) := by rw [the_marriage_closes_for_the_bride n]

theorem the_grounded_groom_satisfies_the_marriage (n : Nat) :
    M (n + 1) = (n + 1) - F (M n) :=
  calc M (n + 1) = (M (n + 1) + F (M n)) - F (M n) :=
        (add_then_sub (M (n + 1)) (F (M n))).symm
    _ = (n + 1) - F (M n) := by rw [the_marriage_closes_for_the_groom n]

theorem every_seat_takes_a_side : ∀ (k : Nat), (∃ j, k = j + j) ∨ (∃ j, k = j + j + 1)
  | 0 => Or.inl ⟨0, rfl⟩
  | k + 1 =>
      match every_seat_takes_a_side k with
      | Or.inl ⟨j, hj⟩ => Or.inr ⟨j, congrArg Nat.succ hj⟩
      | Or.inr ⟨j, hj⟩ => Or.inl ⟨j + 1, by rw [hj, seats_pair j]⟩

theorem the_spouses_disagree_on_a_beacon (k n : Nat)
    (hpage : odometer (n + 1) = beacon k) : M n + 1 = F n := by
  cases every_seat_takes_a_side k with
  | inl h =>
      cases h with
      | intro j hj =>
        rw [hj] at hpage
        show (G n - cond (oddBeacon (odometer (n + 1))) 1 0) + 1
            = G n + cond (evenBeacon (odometer (n + 1))) 1 0
        rw [hpage, the_odd_flag_skips_even_beacons j,
            the_even_flag_flies_on_its_beacon j]
        rfl
  | inr h =>
      cases h with
      | intro j hj =>
        rw [hj] at hpage
        show (G n - cond (oddBeacon (odometer (n + 1))) 1 0) + 1
            = G n + cond (evenBeacon (odometer (n + 1))) 1 0
        rw [hpage, the_odd_flag_flies_on_its_beacon j,
            the_even_flag_skips_odd_beacons j]
        have hpos : 1 ≤ G n := by
          cases n with
          | zero => exact nomatch hpage
          | succ m => exact the_shadow_stays_awake m
        exact sub_one_back (G n) hpos

theorem the_spouses_disagree_exactly_on_the_stairs (k n : Nat)
    (h : n + 1 = fibN (k + 2)) : M n + 1 = F n :=
  the_spouses_disagree_on_a_beacon k n
    (by rw [h]; exact the_odometer_at_a_fibonacci_is_a_beacon k)

theorem the_spouses_agree_between_beacons (n : Nat)
    (he : evenBeacon (odometer (n + 1)) = false)
    (ho : oddBeacon (odometer (n + 1)) = false) : F n = M n := by
  show G n + cond (evenBeacon (odometer (n + 1))) 1 0
      = G n - cond (oddBeacon (odometer (n + 1))) 1 0
  rw [he, ho]
  rfl

theorem back_one_stays_behind : ∀ (x : Nat), x - 1 ≤ x
  | 0 => Nat.le_refl 0
  | x + 1 => Nat.le_add_right x 1

theorem the_toll_never_gains : ∀ (a b : Nat), a - b ≤ a
  | a, 0 => Nat.le_refl a
  | a, b + 1 => Nat.le_trans (back_one_stays_behind (a - b)) (the_toll_never_gains a b)

theorem a_flag_weighs_at_most_one (b : Bool) : cond b 1 0 ≤ 1 := by
  cases b with
  | true => exact Nat.le_refl 1
  | false => exact Nat.zero_le 1

theorem the_walker_leads_the_groom (n : Nat) : M n ≤ G n :=
  the_toll_never_gains (G n) (cond (oddBeacon (odometer (n + 1))) 1 0)

theorem the_bride_leads_the_walker (n : Nat) : G n ≤ F n :=
  Nat.le_add_right (G n) (cond (evenBeacon (odometer (n + 1))) 1 0)

theorem the_groom_follows_the_bride (n : Nat) : M n ≤ F n :=
  Nat.le_trans (the_walker_leads_the_groom n) (the_bride_leads_the_walker n)

theorem the_groom_never_outruns_the_count (n : Nat) : M n ≤ n :=
  Nat.le_trans (the_walker_leads_the_groom n) (the_shadow_never_outruns_the_walker n)

theorem the_bride_never_leaves_reach (n : Nat) : F n ≤ n + 1 :=
  Nat.add_le_add (the_shadow_never_outruns_the_walker n)
    (a_flag_weighs_at_most_one (evenBeacon (odometer (n + 1))))

/-- info: 'Foam.Bridges.the_bride_wakes_lit' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_wakes_lit

/-- info: 'Foam.Bridges.the_groom_wakes_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_wakes_dark

/-- info: 'Foam.Bridges.f_hums_its_opening_bars' does not depend on any axioms -/
#guard_msgs in #print axioms f_hums_its_opening_bars

/-- info: 'Foam.Bridges.m_hums_its_opening_bars' does not depend on any axioms -/
#guard_msgs in #print axioms m_hums_its_opening_bars

/-- info: 'Foam.Bridges.the_bride_reads_the_shared_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_reads_the_shared_page

/-- info: 'Foam.Bridges.the_groom_reads_the_shared_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_reads_the_shared_page

/-- info: 'Foam.Bridges.sub_one_back' does not depend on any axioms -/
#guard_msgs in #print axioms sub_one_back

/-- info: 'Foam.Bridges.the_marriage_closes_for_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms the_marriage_closes_for_the_bride

/-- info: 'Foam.Bridges.the_marriage_closes_for_the_groom' does not depend on any axioms -/
#guard_msgs in #print axioms the_marriage_closes_for_the_groom

/-- info: 'Foam.Bridges.the_grounded_bride_satisfies_the_marriage' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_bride_satisfies_the_marriage

/-- info: 'Foam.Bridges.the_grounded_groom_satisfies_the_marriage' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_groom_satisfies_the_marriage

/-- info: 'Foam.Bridges.every_seat_takes_a_side' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_takes_a_side

/-- info: 'Foam.Bridges.the_spouses_disagree_on_a_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_spouses_disagree_on_a_beacon

/-- info: 'Foam.Bridges.the_spouses_disagree_exactly_on_the_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_spouses_disagree_exactly_on_the_stairs

/-- info: 'Foam.Bridges.the_spouses_agree_between_beacons' does not depend on any axioms -/
#guard_msgs in #print axioms the_spouses_agree_between_beacons

/-- info: 'Foam.Bridges.back_one_stays_behind' does not depend on any axioms -/
#guard_msgs in #print axioms back_one_stays_behind

/-- info: 'Foam.Bridges.the_toll_never_gains' does not depend on any axioms -/
#guard_msgs in #print axioms the_toll_never_gains

/-- info: 'Foam.Bridges.a_flag_weighs_at_most_one' does not depend on any axioms -/
#guard_msgs in #print axioms a_flag_weighs_at_most_one

/-- info: 'Foam.Bridges.the_walker_leads_the_groom' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_leads_the_groom

/-- info: 'Foam.Bridges.the_bride_leads_the_walker' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_leads_the_walker

/-- info: 'Foam.Bridges.the_groom_follows_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_follows_the_bride

/-- info: 'Foam.Bridges.the_groom_never_outruns_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_never_outruns_the_count

/-- info: 'Foam.Bridges.the_bride_never_leaves_reach' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_never_leaves_reach

def peek : List Nat → Nat → Nat
  | [], _ => 1
  | x :: _, 0 => x
  | _ :: rest, i + 1 => peek rest i

def qstep (qs : List Nat) : List Nat :=
  (peek qs (peek qs 0 - 1) + peek qs (peek qs 1 - 1)) :: qs

def qtrace : Nat → List Nat
  | 0 => []
  | 1 => [1]
  | 2 => [1, 1]
  | n + 3 => qstep (qtrace (n + 2))

def Q (n : Nat) : Nat := peek (qtrace n) 0

theorem q_hums_its_opening_bars :
    (Q 1, Q 2, Q 3, Q 4, Q 5, Q 6, Q 7, Q 8, Q 9, Q 10, Q 11, Q 12)
      = (1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 6, 8) := rfl

theorem the_wild_walk_steps_back : Q 16 + 1 = Q 15 := rfl

theorem nothing_from_nothing : ∀ (i : Nat), 0 - i = 0
  | 0 => rfl
  | i + 1 => congrArg Nat.pred (nothing_from_nothing i)

theorem the_trace_remembers : ∀ (n i : Nat), peek (qtrace n) i = Q (n - i)
  | 0, i => by
      show (1 : Nat) = Q (0 - i)
      rw [nothing_from_nothing i]
      rfl
  | 1, 0 => rfl
  | 1, i + 1 => by
      show (1 : Nat) = Q (1 - (i + 1))
      rw [show 1 - (i + 1) = 0 - i from sub_both_tick 0 i, nothing_from_nothing i]
      rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 2, i + 2 => by
      show (1 : Nat) = Q (2 - (i + 2))
      rw [show 2 - (i + 2) = 0 - i from
            (sub_both_tick 1 (i + 1)).trans (sub_both_tick 0 i),
          nothing_from_nothing i]
      rfl
  | n + 3, 0 => rfl
  | n + 3, i + 1 =>
      (the_trace_remembers (n + 2) i).trans
        (congrArg Q (sub_both_tick (n + 2) i)).symm

theorem the_trace_glows : ∀ (n i : Nat), 1 ≤ peek (qtrace n) i
  | 0, _ => Nat.le_refl 1
  | 1, 0 => Nat.le_refl 1
  | 1, _ + 1 => Nat.le_refl 1
  | 2, 0 => Nat.le_refl 1
  | 2, 1 => Nat.le_refl 1
  | 2, _ + 2 => Nat.le_refl 1
  | n + 3, i + 1 => the_trace_glows (n + 2) i
  | n + 3, 0 =>
      Nat.le_trans (the_trace_glows (n + 2) (peek (qtrace (n + 2)) 0 - 1))
        (Nat.le_add_right (peek (qtrace (n + 2)) (peek (qtrace (n + 2)) 0 - 1))
          (peek (qtrace (n + 2)) (peek (qtrace (n + 2)) 1 - 1)))

theorem the_wild_walk_glows (n : Nat) : 1 ≤ Q n := the_trace_glows n 0

theorem step_around_one : ∀ (a b : Nat), 1 ≤ b → (a + 1) - b = a - (b - 1)
  | a, b + 1, _ => sub_both_tick a b
  | _, 0, h => absurd h (Nat.not_succ_le_zero 0)

theorem the_wild_loop_closes_over_the_net (n : Nat) :
    Q (n + 3) = Q ((n + 3) - Q (n + 2)) + Q ((n + 3) - Q (n + 1)) := by
  have hb : peek (qtrace (n + 2)) 1 = Q (n + 1) := the_trace_remembers (n + 2) 1
  have h1 : (n + 3) - Q (n + 2) = (n + 2) - (Q (n + 2) - 1) :=
    step_around_one (n + 2) (Q (n + 2)) (the_wild_walk_glows (n + 2))
  have h2 : (n + 3) - Q (n + 1) = (n + 2) - (Q (n + 1) - 1) :=
    step_around_one (n + 2) (Q (n + 1)) (the_wild_walk_glows (n + 1))
  show peek (qtrace (n + 2)) (Q (n + 2) - 1)
      + peek (qtrace (n + 2)) (peek (qtrace (n + 2)) 1 - 1)
      = Q ((n + 3) - Q (n + 2)) + Q ((n + 3) - Q (n + 1))
  rw [hb, the_trace_remembers (n + 2) (Q (n + 2) - 1),
      the_trace_remembers (n + 2) (Q (n + 1) - 1), h1, h2]

def Surefooted : Prop := ∀ n, Q (n + 1) ≤ n + 1

theorem gap_glows : ∀ (a b : Nat), b + 1 ≤ a → 1 ≤ a - b
  | _, 0, h => h
  | 0, b + 1, h => absurd h (Nat.not_succ_le_zero (b + 1))
  | a + 1, b + 1, h => by
      rw [sub_both_tick a b]
      exact gap_glows a b (Nat.le_of_succ_le_succ h)

theorem a_read_between_the_walls_lands_on_the_page : ∀ (a b : Nat), 1 ≤ b → b ≤ a →
    1 ≤ (a + 1) - b ∧ (a + 1) - b ≤ a
  | a, b + 1, _, hb =>
      ⟨by
        rw [sub_both_tick a b]
        exact gap_glows a b hb,
       by
        rw [sub_both_tick a b]
        exact the_toll_never_gains a b⟩
  | _, 0, h, _ => absurd h (Nat.not_succ_le_zero 0)

theorem sure_feet_keep_every_read_on_the_page (hs : Surefooted) (n : Nat) :
    (1 ≤ (n + 3) - Q (n + 2) ∧ (n + 3) - Q (n + 2) ≤ n + 2)
      ∧ (1 ≤ (n + 3) - Q (n + 1) ∧ (n + 3) - Q (n + 1) ≤ n + 2) :=
  ⟨a_read_between_the_walls_lands_on_the_page (n + 2) (Q (n + 2))
      (the_wild_walk_glows (n + 2)) (hs (n + 1)),
   a_read_between_the_walls_lands_on_the_page (n + 2) (Q (n + 1))
      (the_wild_walk_glows (n + 1))
      (Nat.le_trans (hs n) (Nat.le_add_right (n + 1) 1))⟩

def surefootedTo : Nat → Bool
  | 0 => true
  | n + 1 => Nat.ble (Q (n + 1)) (n + 1) && surefootedTo n

theorem the_wild_walk_keeps_its_feet_for_a_fibonacci_of_steps :
    surefootedTo 34 = true := rfl

/-- info: 'Foam.Bridges.q_hums_its_opening_bars' does not depend on any axioms -/
#guard_msgs in #print axioms q_hums_its_opening_bars

/-- info: 'Foam.Bridges.the_wild_walk_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_steps_back

/-- info: 'Foam.Bridges.nothing_from_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_from_nothing

/-- info: 'Foam.Bridges.the_trace_remembers' does not depend on any axioms -/
#guard_msgs in #print axioms the_trace_remembers

/-- info: 'Foam.Bridges.the_trace_glows' does not depend on any axioms -/
#guard_msgs in #print axioms the_trace_glows

/-- info: 'Foam.Bridges.the_wild_walk_glows' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_glows

/-- info: 'Foam.Bridges.step_around_one' does not depend on any axioms -/
#guard_msgs in #print axioms step_around_one

/-- info: 'Foam.Bridges.the_wild_loop_closes_over_the_net' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_loop_closes_over_the_net

/-- info: 'Foam.Bridges.gap_glows' does not depend on any axioms -/
#guard_msgs in #print axioms gap_glows

/-- info: 'Foam.Bridges.a_read_between_the_walls_lands_on_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms a_read_between_the_walls_lands_on_the_page

/-- info: 'Foam.Bridges.sure_feet_keep_every_read_on_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms sure_feet_keep_every_read_on_the_page

/-- info: 'Foam.Bridges.the_wild_walk_keeps_its_feet_for_a_fibonacci_of_steps' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_keeps_its_feet_for_a_fibonacci_of_steps

def tstep (qs : List Nat) : List Nat :=
  (peek qs (peek qs 0) + peek qs (peek qs 1 + 1)) :: qs

def ttrace : Nat → List Nat
  | 0 => []
  | 1 => [1]
  | 2 => [1, 1]
  | n + 3 => tstep (ttrace (n + 2))

def T (n : Nat) : Nat := peek (ttrace n) 0

def slack (n : Nat) : Nat := n - T n

theorem t_hums_its_opening_bars :
    (T 1, T 2, T 3, T 4, T 5, T 6, T 7, T 8, T 9, T 10, T 11, T 12)
      = (1, 1, 2, 2, 2, 3, 4, 4, 4, 4, 5, 6) := rfl

theorem the_tame_trace_remembers : ∀ (n i : Nat), peek (ttrace n) i = T (n - i)
  | 0, i => by
      show (1 : Nat) = T (0 - i)
      rw [nothing_from_nothing i]
      rfl
  | 1, 0 => rfl
  | 1, i + 1 => by
      show (1 : Nat) = T (1 - (i + 1))
      rw [show 1 - (i + 1) = 0 - i from sub_both_tick 0 i, nothing_from_nothing i]
      rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 2, i + 2 => by
      show (1 : Nat) = T (2 - (i + 2))
      rw [show 2 - (i + 2) = 0 - i from
            (sub_both_tick 1 (i + 1)).trans (sub_both_tick 0 i),
          nothing_from_nothing i]
      rfl
  | n + 3, 0 => rfl
  | n + 3, i + 1 =>
      (the_tame_trace_remembers (n + 2) i).trans
        (congrArg T (sub_both_tick (n + 2) i)).symm

theorem the_tame_trace_glows : ∀ (n i : Nat), 1 ≤ peek (ttrace n) i
  | 0, _ => Nat.le_refl 1
  | 1, 0 => Nat.le_refl 1
  | 1, _ + 1 => Nat.le_refl 1
  | 2, 0 => Nat.le_refl 1
  | 2, 1 => Nat.le_refl 1
  | 2, _ + 2 => Nat.le_refl 1
  | n + 3, i + 1 => the_tame_trace_glows (n + 2) i
  | n + 3, 0 =>
      Nat.le_trans (the_tame_trace_glows (n + 2) (peek (ttrace (n + 2)) 0))
        (Nat.le_add_right (peek (ttrace (n + 2)) (peek (ttrace (n + 2)) 0))
          (peek (ttrace (n + 2)) (peek (ttrace (n + 2)) 1 + 1)))

theorem the_tame_walk_glows (n : Nat) : 1 ≤ T n := the_tame_trace_glows n 0

theorem the_tame_loop_closes_over_the_net (n : Nat) :
    T (n + 3) = T ((n + 2) - T (n + 2)) + T ((n + 1) - T (n + 1)) := by
  have hb : peek (ttrace (n + 2)) 1 = T (n + 1) := the_tame_trace_remembers (n + 2) 1
  show peek (ttrace (n + 2)) (T (n + 2))
      + peek (ttrace (n + 2)) (peek (ttrace (n + 2)) 1 + 1)
      = T ((n + 2) - T (n + 2)) + T ((n + 1) - T (n + 1))
  rw [hb, the_tame_trace_remembers (n + 2) (T (n + 2)),
      the_tame_trace_remembers (n + 2) (T (n + 1) + 1),
      show (n + 2) - (T (n + 1) + 1) = (n + 1) - T (n + 1) from
        sub_both_tick (n + 1) (T (n + 1))]

theorem the_tame_walk_touches_the_net_once : T 3 = T 1 + T 0 := rfl

/-- info: 'Foam.Bridges.t_hums_its_opening_bars' does not depend on any axioms -/
#guard_msgs in #print axioms t_hums_its_opening_bars

/-- info: 'Foam.Bridges.the_tame_trace_remembers' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_trace_remembers

/-- info: 'Foam.Bridges.the_tame_trace_glows' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_trace_glows

/-- info: 'Foam.Bridges.the_tame_walk_glows' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_glows

/-- info: 'Foam.Bridges.the_tame_loop_closes_over_the_net' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_loop_closes_over_the_net

/-- info: 'Foam.Bridges.the_tame_walk_touches_the_net_once' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_touches_the_net_once

theorem under_the_wire : ∀ (k m : Nat), k ≤ m + 1 → k ≤ m ∨ k = m + 1
  | 0, m, _ => Or.inl (Nat.zero_le m)
  | k + 1, 0, h =>
      match k, Nat.le_of_succ_le_succ h with
      | 0, _ => Or.inr rfl
      | k + 1, h' => absurd h' (Nat.not_succ_le_zero k)
  | k + 1, m + 1, h =>
      match under_the_wire k m (Nat.le_of_succ_le_succ h) with
      | Or.inl h' => Or.inl (Nat.succ_le_succ h')
      | Or.inr e => Or.inr (congrArg (· + 1) e)

theorem halves_agree : ∀ (a b : Nat), a + a = b + b → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | a + 1, b + 1, h =>
      congrArg (· + 1)
        (halves_agree a b
          (Nat.succ.inj
            ((Nat.succ_add a a).symm.trans
              ((Nat.succ.inj h).trans (Nat.succ_add b b)))))

theorem carry_the_one (x y : Nat) : (x + y) + x = (x + x) + y := by
  rw [Nat.add_assoc x y x, Nat.add_comm y x, ← Nat.add_assoc x x y]

theorem double_the_step (x : Nat) : (x + 1) + (x + 1) = (x + x) + 2 :=
  congrArg (· + 1) (carry_the_one x 1)

theorem pair_up (a b : Nat) : (a + b) + (a + b) = (a + a) + (b + b) := by
  rw [Nat.add_assoc a b (a + b), ← Nat.add_assoc b a b, Nat.add_comm b a,
      Nat.add_assoc a b b, ← Nat.add_assoc a a (b + b)]

theorem a_step_widens_the_gap : ∀ (a b : Nat), b ≤ a → (a + 1) - b = (a - b) + 1
  | _, 0, _ => rfl
  | 0, b + 1, h => absurd h (Nat.not_succ_le_zero b)
  | a + 1, b + 1, h => by
      rw [sub_both_tick (a + 1) b, sub_both_tick a b]
      exact a_step_widens_the_gap a b (Nat.le_of_succ_le_succ h)

theorem the_low_read_stays_on_the_page : ∀ (a b : Nat), 1 ≤ b →
    ((a + 1) - b) + 1 ≤ a + 1
  | a, b + 1, _ => by
      rw [sub_both_tick a b]
      exact Nat.succ_le_succ (the_toll_never_gains a b)
  | _, 0, h => absurd h (Nat.not_succ_le_zero 0)

theorem slack_holds_on_a_step (n : Nat) (h : T (n + 1) = T n + 1) :
    slack (n + 1) = slack n := by
  show (n + 1) - T (n + 1) = n - T n
  rw [h]
  exact sub_both_tick n (T n)

theorem slack_slides_on_a_flat (n : Nat) (h : T (n + 1) = T n) (hle : T n ≤ n) :
    slack (n + 1) = slack n + 1 := by
  show (n + 1) - T (n + 1) = (n - T n) + 1
  rw [h]
  exact a_step_widens_the_gap n (T n) hle

/-- info: 'Foam.Bridges.under_the_wire' does not depend on any axioms -/
#guard_msgs in #print axioms under_the_wire

/-- info: 'Foam.Bridges.halves_agree' does not depend on any axioms -/
#guard_msgs in #print axioms halves_agree

/-- info: 'Foam.Bridges.carry_the_one' does not depend on any axioms -/
#guard_msgs in #print axioms carry_the_one

/-- info: 'Foam.Bridges.double_the_step' does not depend on any axioms -/
#guard_msgs in #print axioms double_the_step

/-- info: 'Foam.Bridges.pair_up' does not depend on any axioms -/
#guard_msgs in #print axioms pair_up

/-- info: 'Foam.Bridges.a_step_widens_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms a_step_widens_the_gap

/-- info: 'Foam.Bridges.the_low_read_stays_on_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_low_read_stays_on_the_page

/-- info: 'Foam.Bridges.slack_holds_on_a_step' does not depend on any axioms -/
#guard_msgs in #print axioms slack_holds_on_a_step

/-- info: 'Foam.Bridges.slack_slides_on_a_flat' does not depend on any axioms -/
#guard_msgs in #print axioms slack_slides_on_a_flat

def coasting (n : Nat) : Prop :=
  T (n + 3) = T (n + 2)
    ∧ T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2)
    ∧ T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3)

def gathering (n : Nat) : Prop :=
  T (n + 3) = T (n + 2)
    ∧ T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2)
    ∧ T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) + 2

def springing (n : Nat) : Prop :=
  T (n + 3) = T (n + 2) + 1
    ∧ T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2) + 2
    ∧ T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) + 1

def landing (n : Nat) : Prop :=
  T (n + 3) = T (n + 2) + 1
    ∧ T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2) + 1
    ∧ T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3)

def gait (n : Nat) : Prop := coasting n ∨ gathering n ∨ springing n ∨ landing n

def paced (n : Nat) : Prop :=
  (∀ k, k + 1 ≤ n + 3 → T (k + 1) = T k ∨ T (k + 1) = T k + 1)
    ∧ T (n + 3) ≤ n + 3
    ∧ gait n

theorem paced_step (n : Nat) : paced n → paced (n + 1) := by
  intro h
  have steps := h.1
  have sure := h.2.1
  have loop : T ((n + 3) + 1) = T (slack (n + 3)) + T (slack (n + 2)) :=
    the_tame_loop_closes_over_the_net (n + 1)
  have glow3 : 1 ≤ T (n + 3) := the_tame_walk_glows (n + 3)
  have finish : (T ((n + 3) + 1) = T (n + 3) ∨ T ((n + 3) + 1) = T (n + 3) + 1) →
      gait (n + 1) → paced (n + 1) := by
    intro hstep st'
    refine ⟨?_, ?_, st'⟩
    · intro k hk
      match under_the_wire (k + 1) (n + 3) hk with
      | Or.inl h' => exact steps k h'
      | Or.inr e =>
          have ek : k = n + 3 := Nat.succ.inj e
          rw [ek]
          exact hstep
    · match hstep with
      | Or.inl e =>
          show T ((n + 3) + 1) ≤ (n + 3) + 1
          rw [e]
          exact Nat.le_trans sure (Nat.le_succ (n + 3))
      | Or.inr e =>
          show T ((n + 3) + 1) ≤ (n + 3) + 1
          rw [e]
          exact Nat.succ_le_succ sure
  have flat_case : T ((n + 3) + 1) = T (n + 3) →
      T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) → paced (n + 1) := by
    intro hflat hd3
    have hslide : slack ((n + 3) + 1) = slack (n + 3) + 1 :=
      slack_slides_on_a_flat (n + 3) hflat sure
    have hread := steps (slack (n + 3))
      (the_low_read_stays_on_the_page (n + 2) (T (n + 3)) glow3)
    match hread with
    | Or.inl hb =>
        exact finish (Or.inl hflat)
          (Or.inl ⟨hflat, hd3, by
            show T (slack ((n + 3) + 1)) + T (slack ((n + 3) + 1)) = T ((n + 3) + 1)
            rw [hslide, hb, hd3, hflat]⟩)
    | Or.inr hb =>
        exact finish (Or.inl hflat)
          (Or.inr (Or.inl ⟨hflat, hd3, by
            show T (slack ((n + 3) + 1)) + T (slack ((n + 3) + 1)) = T ((n + 3) + 1) + 2
            rw [hslide, hb, double_the_step, hd3, hflat]⟩))
  match h.2.2 with
  | Or.inl hA =>
      have hU : T (n + 3) = T (n + 2) := hA.1
      have hd2 : T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2) := hA.2.1
      have hd3 : T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) := hA.2.2
      exact flat_case (halves_agree _ _ (by rw [loop, pair_up, hd3, hd2, hU])) hd3
  | Or.inr (Or.inl hB) =>
      have hU : T (n + 3) = T (n + 2) := hB.1
      have hd2 : T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2) := hB.2.1
      have hd3 : T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) + 2 := hB.2.2
      have hup : T ((n + 3) + 1) = T (n + 3) + 1 :=
        halves_agree _ _ (by
          rw [loop, pair_up, hd3, hd2, ← hU, carry_the_one (T (n + 3)) 2,
              double_the_step])
      have hhold : slack ((n + 3) + 1) = slack (n + 3) :=
        slack_holds_on_a_step (n + 3) hup
      exact finish (Or.inr hup)
        (Or.inr (Or.inr (Or.inl ⟨hup, hd3, by
          show T (slack ((n + 3) + 1)) + T (slack ((n + 3) + 1)) = T ((n + 3) + 1) + 1
          rw [hhold, hd3, hup]⟩)))
  | Or.inr (Or.inr (Or.inl hC)) =>
      have hU : T (n + 3) = T (n + 2) + 1 := hC.1
      have hd2 : T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2) + 2 := hC.2.1
      have hd3 : T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) + 1 := hC.2.2
      have hup : T ((n + 3) + 1) = T (n + 3) + 1 :=
        halves_agree _ _ (by rw [loop, pair_up, hd3, hd2, hU])
      have hhold : slack ((n + 3) + 1) = slack (n + 3) :=
        slack_holds_on_a_step (n + 3) hup
      exact finish (Or.inr hup)
        (Or.inr (Or.inr (Or.inr ⟨hup, hd3, by
          show T (slack ((n + 3) + 1)) + T (slack ((n + 3) + 1)) = T ((n + 3) + 1)
          rw [hhold, hd3, hup]⟩)))
  | Or.inr (Or.inr (Or.inr hD)) =>
      have hU : T (n + 3) = T (n + 2) + 1 := hD.1
      have hd2 : T (slack (n + 2)) + T (slack (n + 2)) = T (n + 2) + 1 := hD.2.1
      have hd3 : T (slack (n + 3)) + T (slack (n + 3)) = T (n + 3) := hD.2.2
      exact flat_case (halves_agree _ _ (by rw [loop, pair_up, hd3, hd2, ← hU])) hd3

theorem the_tame_walk_keeps_its_gait : ∀ (n : Nat), paced n
  | 0 =>
      ⟨fun k hk =>
        match k, hk with
        | 0, _ => Or.inl rfl
        | 1, _ => Or.inl rfl
        | 2, _ => Or.inr rfl
        | k + 3, hk =>
            absurd
              (Nat.le_of_succ_le_succ
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))
              (Nat.not_succ_le_zero k),
       Nat.le_succ 2,
       Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩
  | n + 1 => paced_step n (the_tame_walk_keeps_its_gait n)

/-- info: 'Foam.Bridges.paced_step' does not depend on any axioms -/
#guard_msgs in #print axioms paced_step

/-- info: 'Foam.Bridges.the_tame_walk_keeps_its_gait' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_keeps_its_gait

theorem the_tame_walk_never_steps_back (n : Nat) : T n ≤ T (n + 1) := by
  match (the_tame_walk_keeps_its_gait n).1 n (Nat.le_add_right (n + 1) 2) with
  | Or.inl e => exact Nat.le_of_eq e.symm
  | Or.inr e =>
      rw [e]
      exact Nat.le_succ (T n)

theorem the_tame_walk_never_skips (n : Nat) : T (n + 1) ≤ T n + 1 := by
  match (the_tame_walk_keeps_its_gait n).1 n (Nat.le_add_right (n + 1) 2) with
  | Or.inl e =>
      rw [e]
      exact Nat.le_succ (T n)
  | Or.inr e => exact Nat.le_of_eq e

theorem the_tame_cousin_is_surefooted : ∀ (n : Nat), T (n + 1) ≤ n + 1
  | 0 => Nat.le_refl 1
  | 1 => Nat.le_succ 1
  | 2 => Nat.le_succ 2
  | n + 3 => (the_tame_walk_keeps_its_gait (n + 1)).2.1

theorem the_tame_walk_stays_a_step_behind : ∀ (n : Nat), T (n + 2) ≤ n + 1
  | 0 => Nat.le_refl 1
  | n + 1 =>
      Nat.le_trans (the_tame_walk_never_skips (n + 2))
        (Nat.succ_le_succ (the_tame_walk_stays_a_step_behind n))

theorem the_tame_walk_needs_no_net (n : Nat) :
    1 ≤ (n + 2) - T (n + 2) ∧ (n + 2) - T (n + 2) ≤ n + 1 :=
  ⟨gap_glows (n + 2) (T (n + 2))
      (Nat.succ_le_succ (the_tame_walk_stays_a_step_behind n)),
   Nat.le_of_succ_le_succ
      (the_low_read_stays_on_the_page (n + 1) (T (n + 2)) (the_tame_walk_glows (n + 2)))⟩

/-- info: 'Foam.Bridges.the_tame_walk_never_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_never_steps_back

/-- info: 'Foam.Bridges.the_tame_walk_never_skips' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_never_skips

/-- info: 'Foam.Bridges.the_tame_cousin_is_surefooted' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_cousin_is_surefooted

/-- info: 'Foam.Bridges.the_tame_walk_stays_a_step_behind' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_stays_a_step_behind

/-- info: 'Foam.Bridges.the_tame_walk_needs_no_net' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_needs_no_net

def bodometer : Nat → List Bool
  | 0 => []
  | n + 1 => bclick (bodometer n)

theorem the_bodometer_reads_true : ∀ (n : Nat), gauge 0 (bodometer n) = n
  | 0 => rfl
  | n + 1 => by
      show gauge 0 (bclick (bodometer n)) = n + 1
      rw [a_click_deposits_one_notch (bodometer n) 0, the_bodometer_reads_true n]
      exact Nat.add_comm 1 n

theorem the_gate_reads_the_parity : ∀ (u : Nat),
    bodometer (u + u + 1) = true :: bodometer u
      ∧ bodometer (u + u + 2) = false :: bodometer (u + 1)
  | 0 => ⟨rfl, rfl⟩
  | u + 1 => by
      have ih := the_gate_reads_the_parity u
      have hidx : (u + 1) + (u + 1) = u + u + 2 := Nat.succ_add u (u + 1)
      constructor
      · rw [hidx]
        show bclick (bodometer (u + u + 2)) = true :: bodometer (u + 1)
        rw [ih.2]
        rfl
      · rw [hidx]
        show bclick (bodometer (u + u + 3)) = false :: bodometer (u + 2)
        rw [show bodometer (u + u + 3) = true :: bodometer (u + 1) from by
              show bclick (bodometer (u + u + 2)) = true :: bodometer (u + 1)
              rw [ih.2]
              rfl]
        rfl

theorem an_odd_count_lights_the_gate (u : Nat) :
    bodometer (u + u + 1) = true :: bodometer u := (the_gate_reads_the_parity u).1

theorem an_even_count_rests_the_gate (u : Nat) :
    bodometer (u + u + 2) = false :: bodometer (u + 1) := (the_gate_reads_the_parity u).2

/-- info: 'Foam.Bridges.the_bodometer_reads_true' does not depend on any axioms -/
#guard_msgs in #print axioms the_bodometer_reads_true

/-- info: 'Foam.Bridges.the_gate_reads_the_parity' does not depend on any axioms -/
#guard_msgs in #print axioms the_gate_reads_the_parity

/-- info: 'Foam.Bridges.an_odd_count_lights_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms an_odd_count_lights_the_gate

/-- info: 'Foam.Bridges.an_even_count_rests_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms an_even_count_rests_the_gate

def mtime : Nat → Nat
  | 0 => 0
  | n + 1 => mtime n + beat (bodometer n)

theorem the_clock_hums_the_ruler :
    (mtime 1, mtime 2, mtime 3, mtime 4, mtime 5, mtime 6, mtime 7, mtime 8)
      = (2, 5, 6, 10, 11, 13, 14, 19) := rfl

theorem the_clock_folds_at_its_half : ∀ (u : Nat),
    mtime (u + u + 1) = mtime u + (u + u + 2)
      ∧ mtime (u + u + 2) = mtime (u + 1) + (u + u + 3)
  | 0 => ⟨rfl, rfl⟩
  | u + 1 => by
      have ih := the_clock_folds_at_its_half u
      have hidx : (u + 1) + (u + 1) = u + u + 2 := Nat.succ_add u (u + 1)
      have h1 : mtime (u + u + 3) = mtime (u + 1) + (u + u + 4) := by
        show mtime (u + u + 2) + beat (bodometer (u + u + 2)) = mtime (u + 1) + (u + u + 4)
        rw [an_even_count_rests_the_gate u, ih.2]
        rfl
      have h2 : mtime (u + u + 4) = mtime (u + 2) + (u + u + 5) := by
        show mtime (u + u + 3) + beat (bodometer (u + u + 3)) = mtime (u + 2) + (u + u + 5)
        rw [show bodometer (u + u + 3) = true :: bodometer (u + 1) from by
              show bclick (bodometer (u + u + 2)) = true :: bodometer (u + 1)
              rw [an_even_count_rests_the_gate u]
              rfl,
            h1]
        show mtime (u + 1) + (u + u + 4) + (beat (bodometer (u + 1)) + 1)
          = mtime (u + 1) + beat (bodometer (u + 1)) + (u + u + 5)
        exact add_shuffle (mtime (u + 1)) (u + u + 4) (beat (bodometer (u + 1))) 1
      constructor
      · rw [hidx]
        exact h1
      · rw [hidx]
        exact h2

theorem stack_right : ∀ (a b c : Nat), a ≤ b → a + c ≤ b + c
  | _, _, 0, h => h
  | a, b, c + 1, h => Nat.succ_le_succ (stack_right a b c h)

theorem stack_left (a b c : Nat) (h : b ≤ c) : a + b ≤ a + c := by
  rw [Nat.add_comm a b, Nat.add_comm a c]
  exact stack_right b c a h

theorem the_clock_never_stalls (v : Nat) : mtime v < mtime (v + 1) := by
  show mtime v + 1 ≤ mtime v + beat (bodometer v)
  exact stack_left (mtime v) 1 (beat (bodometer v)) (every_beat_ticks (bodometer v))

/-- info: 'Foam.Bridges.the_clock_hums_the_ruler' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_hums_the_ruler

/-- info: 'Foam.Bridges.the_clock_folds_at_its_half' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_folds_at_its_half

/-- info: 'Foam.Bridges.stack_right' does not depend on any axioms -/
#guard_msgs in #print axioms stack_right

/-- info: 'Foam.Bridges.stack_left' does not depend on any axioms -/
#guard_msgs in #print axioms stack_left

/-- info: 'Foam.Bridges.the_clock_never_stalls' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_never_stalls

theorem unstack : ∀ (a b c : Nat), a + c = b + c → a = b
  | _, _, 0, h => h
  | a, b, c + 1, h => unstack a b c (Nat.succ.inj h)

theorem the_clock_charges_twice_less_the_light : ∀ (n : Nat),
    mtime n + ones (bodometer n) = n + n + (bodometer n).length
  | 0 => rfl
  | n + 1 => by
      apply unstack _ _ (bodometer n).length
      show mtime n + beat (bodometer n) + ones (bclick (bodometer n)) + (bodometer n).length
        = (n + 1) + (n + 1) + (bclick (bodometer n)).length + (bodometer n).length
      rw [Nat.add_assoc (mtime n) (beat (bodometer n)) (ones (bclick (bodometer n))),
          Nat.add_comm (beat (bodometer n)) (ones (bclick (bodometer n))),
          Nat.add_assoc (mtime n) (ones (bclick (bodometer n)) + beat (bodometer n))
            (bodometer n).length,
          the_carry_bills_its_erasures (bodometer n),
          Nat.add_assoc (ones (bodometer n)) 2 (bclick (bodometer n)).length,
          ← Nat.add_assoc (mtime n) (ones (bodometer n)) (2 + (bclick (bodometer n)).length),
          the_clock_charges_twice_less_the_light n,
          double_the_step n,
          add_shuffle (n + n) (bodometer n).length 2 (bclick (bodometer n)).length,
          Nat.add_comm (bodometer n).length (bclick (bodometer n)).length,
          ← Nat.add_assoc (n + n + 2) (bclick (bodometer n)).length (bodometer n).length]

/-- info: 'Foam.Bridges.unstack' does not depend on any axioms -/
#guard_msgs in #print axioms unstack

/-- info: 'Foam.Bridges.the_clock_charges_twice_less_the_light' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_charges_twice_less_the_light

theorem pull_out_the_middle (a b c : Nat) : a + b + c - b = a + c := by
  rw [Nat.add_assoc a b c, Nat.add_comm b c, ← Nat.add_assoc a c b]
  exact add_then_sub (a + c) b

theorem a_tick_is_a_step : ∀ (m : Nat), 1 ≤ m → ∃ c, m = c + 1
  | m + 1, _ => ⟨m, rfl⟩
  | 0, h => absurd h (Nat.not_succ_le_zero 0)

theorem every_count_finds_its_door : ∀ (v : Nat),
    v = 0 ∨ v = 1 ∨ (∃ t, v = t + t + 2) ∨ (∃ t, v = t + t + 3)
  | 0 => Or.inl rfl
  | 1 => Or.inr (Or.inl rfl)
  | 2 => Or.inr (Or.inr (Or.inl ⟨0, rfl⟩))
  | 3 => Or.inr (Or.inr (Or.inr ⟨0, rfl⟩))
  | v + 4 =>
      match every_count_finds_its_door (v + 2) with
      | Or.inl h => Or.inr (Or.inr (Or.inl ⟨0, congrArg (· + 2) h⟩))
      | Or.inr (Or.inl h) => Or.inr (Or.inr (Or.inr ⟨0, congrArg (· + 2) h⟩))
      | Or.inr (Or.inr (Or.inl ⟨t, h⟩)) =>
          Or.inr (Or.inr (Or.inl ⟨t + 1,
            (congrArg (· + 2) h).trans (congrArg (· + 2) (Nat.succ_add t (t + 1))).symm⟩))
      | Or.inr (Or.inr (Or.inr ⟨t, h⟩)) =>
          Or.inr (Or.inr (Or.inr ⟨t + 1,
            (congrArg (· + 2) h).trans (congrArg (· + 3) (Nat.succ_add t (t + 1))).symm⟩))

/-- info: 'Foam.Bridges.pull_out_the_middle' does not depend on any axioms -/
#guard_msgs in #print axioms pull_out_the_middle

/-- info: 'Foam.Bridges.a_tick_is_a_step' does not depend on any axioms -/
#guard_msgs in #print axioms a_tick_is_a_step

/-- info: 'Foam.Bridges.every_count_finds_its_door' does not depend on any axioms -/
#guard_msgs in #print axioms every_count_finds_its_door

def metered (n : Nat) : Prop :=
  ∀ v j, j < beat (bodometer v) → mtime v + j + 1 ≤ n → T (mtime v + j + 1) = v + 1

theorem metered_step (n : Nat) (ih : metered n) : metered (n + 1) := by
  intro v j hj hle
  match every_count_finds_its_door v with
  | Or.inl hv =>
      subst hv
      match j, hj with
      | 0, _ => rfl
      | 1, _ => rfl
      | j + 2, hjj =>
          exact absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hjj))
            (Nat.not_succ_le_zero j)
  | Or.inr (Or.inl hv) =>
      subst hv
      match j, hj with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | j + 3, hjj =>
          exact absurd
            (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hjj)))
            (Nat.not_succ_le_zero j)
  | Or.inr (Or.inr (Or.inl ⟨t, hv⟩)) =>
      subst hv
      have hb1 : beat (bodometer (t + t + 2)) = 1 := by
        rw [an_even_count_rests_the_gate t]
        rfl
      rw [hb1] at hj
      match j, hj with
      | j + 1, hjj =>
          exact absurd (Nat.le_of_succ_le_succ hjj) (Nat.not_succ_le_zero j)
      | 0, _ =>
          obtain ⟨c, hc⟩ :=
            a_tick_is_a_step (beat (bodometer t)) (every_beat_ticks (bodometer t))
          have hM1 : mtime (t + t + 1) = mtime t + (t + t + 2) :=
            (the_clock_folds_at_its_half t).1
          have hM2 : mtime (t + t + 2) = mtime t + (t + t + 2) + (c + 2) := by
            show mtime (t + t + 1) + beat (bodometer (t + t + 1))
              = mtime t + (t + t + 2) + (c + 2)
            rw [an_odd_count_lights_the_gate t, hM1]
            show mtime t + (t + t + 2) + (beat (bodometer t) + 1)
              = mtime t + (t + t + 2) + (c + 2)
            rw [hc]
          have hle' : mtime t + (t + t + 2) + c + 2 ≤ n := by
            have h := hle
            rw [hM2] at h
            exact Nat.le_of_succ_le_succ h
          have hfloor : mtime t + c + 2 ≤ n :=
            Nat.le_trans
              (stack_right (mtime t + c) (mtime t + (t + t + 2) + c) 2
                (stack_right (mtime t) (mtime t + (t + t + 2)) c
                  (Nat.le_add_right (mtime t) (t + t + 2))))
              hle'
          have h1 : T (mtime t + (t + t + 2) + c + 2) = t + t + 2 := by
            have h := ih (t + t + 1) (c + 1)
              (by rw [an_odd_count_lights_the_gate t]
                  show c + 1 < beat (bodometer t) + 1
                  rw [hc]
                  exact Nat.le_refl (c + 2))
              (by rw [hM1]; exact hle')
            rw [hM1] at h
            exact h
          have h2 : T (mtime t + (t + t + 2) + c + 1) = t + t + 2 := by
            have h := ih (t + t + 1) c
              (by rw [an_odd_count_lights_the_gate t]
                  show c < beat (bodometer t) + 1
                  rw [hc]
                  exact Nat.le_succ (c + 1))
              (by rw [hM1]
                  exact Nat.le_trans (Nat.le_succ (mtime t + (t + t + 2) + c + 1)) hle')
            rw [hM1] at h
            exact h
          have h3 : T (mtime t + c + 2) = t + 2 := by
            have h := ih (t + 1) 0 (every_beat_ticks (bodometer (t + 1)))
              (by show mtime t + beat (bodometer t) + 0 + 1 ≤ n
                  rw [hc]
                  exact hfloor)
            rw [show mtime t + c + 2 = mtime (t + 1) + 0 + 1 from by
                  show mtime t + c + 2 = mtime t + beat (bodometer t) + 0 + 1
                  rw [hc]
                  rfl]
            exact h
          have h4 : T (mtime t + c + 1) = t + 1 :=
            ih t c (by rw [hc]; exact Nat.le_refl (c + 1))
              (Nat.le_trans (Nat.le_succ (mtime t + c + 1)) hfloor)
          rw [hM2]
          show T (mtime t + (t + t + 2) + c + 3) = t + t + 3
          rw [the_tame_loop_closes_over_the_net (mtime t + (t + t + 2) + c), h1, h2,
              show mtime t + (t + t + 2) + c + 2 - (t + t + 2) = mtime t + c + 2 from
                pull_out_the_middle (mtime t) (t + t + 2) (c + 2),
              show mtime t + (t + t + 2) + c + 1 - (t + t + 2) = mtime t + c + 1 from
                pull_out_the_middle (mtime t) (t + t + 2) (c + 1),
              h3, h4]
          exact congrArg (· + 1) (carry_the_one t 2)
  | Or.inr (Or.inr (Or.inr ⟨t, hv⟩)) =>
      subst hv
      have hg3 : bodometer (t + t + 3) = true :: bodometer (t + 1) := by
        show bclick (bodometer (t + t + 2)) = true :: bodometer (t + 1)
        rw [an_even_count_rests_the_gate t]
        rfl
      have hb3 : beat (bodometer (t + t + 3)) = beat (bodometer (t + 1)) + 1 := by
        rw [hg3]
        rfl
      have hM3 : mtime (t + t + 3) = mtime (t + 1) + (t + t + 4) := by
        show mtime (t + t + 2) + beat (bodometer (t + t + 2))
          = mtime (t + 1) + (t + t + 4)
        rw [an_even_count_rests_the_gate t, (the_clock_folds_at_its_half t).2]
        rfl
      rw [hb3] at hj
      match j, hj with
      | 0, _ =>
          obtain ⟨c, hc⟩ :=
            a_tick_is_a_step (beat (bodometer t)) (every_beat_ticks (bodometer t))
          have hle' : mtime (t + 1) + (t + t + 2) + 2 ≤ n := by
            have h := hle
            rw [hM3] at h
            exact Nat.le_of_succ_le_succ h
          have h1 : T (mtime (t + 1) + (t + t + 2) + 2) = t + t + 3 := by
            have h := ih (t + t + 2) 0 (every_beat_ticks (bodometer (t + t + 2)))
              (by rw [(the_clock_folds_at_its_half t).2]; exact hle')
            rw [(the_clock_folds_at_its_half t).2] at h
            exact h
          have h2 : T (mtime (t + 1) + (t + t + 2) + 1) = t + t + 2 := by
            have hpos : mtime (t + 1) + (t + t + 2) + 1 = mtime (t + t + 1) + (c + 1) + 1 := by
              rw [(the_clock_folds_at_its_half t).1]
              show mtime t + beat (bodometer t) + (t + t + 2) + 1
                = mtime t + (t + t + 2) + (c + 1) + 1
              rw [hc]
              exact add_shuffle (mtime t) (c + 1) (t + t + 2) 1
            rw [hpos]
            exact ih (t + t + 1) (c + 1)
              (by rw [an_odd_count_lights_the_gate t]
                  show c + 1 < beat (bodometer t) + 1
                  rw [hc]
                  exact Nat.le_refl (c + 2))
              (by rw [← hpos]
                  exact Nat.le_trans (Nat.le_succ (mtime (t + 1) + (t + t + 2) + 1)) hle')
          have h3 : T (mtime (t + 1) + 1) = t + 2 :=
            ih (t + 1) 0 (every_beat_ticks (bodometer (t + 1)))
              (Nat.le_trans
                (stack_left (mtime (t + 1)) 1 (t + t + 4) (Nat.le_add_left 1 (t + t + 3)))
                hle')
          rw [hM3]
          show T (mtime (t + 1) + (t + t + 2) + 3) = t + t + 4
          rw [the_tame_loop_closes_over_the_net (mtime (t + 1) + (t + t + 2)), h1, h2,
              show mtime (t + 1) + (t + t + 2) + 2 - (t + t + 3) = mtime (t + 1) + 1 from
                pull_out_the_middle (mtime (t + 1)) (t + t + 3) 1,
              show mtime (t + 1) + (t + t + 2) + 1 - (t + t + 2) = mtime (t + 1) + 1 from
                pull_out_the_middle (mtime (t + 1)) (t + t + 2) 1,
              h3]
          exact congrArg (· + 2) (carry_the_one t 2)
      | 1, _ =>
          have hle' : mtime (t + 1) + (t + t + 3) + 2 ≤ n := by
            have h := hle
            rw [hM3] at h
            exact Nat.le_of_succ_le_succ h
          have h1 : T (mtime (t + 1) + (t + t + 3) + 2) = t + t + 4 := by
            have h := ih (t + t + 3) 0 (every_beat_ticks (bodometer (t + t + 3)))
              (by rw [hM3]; exact hle')
            rw [hM3] at h
            exact h
          have h2 : T (mtime (t + 1) + (t + t + 3) + 1) = t + t + 3 := by
            have h := ih (t + t + 2) 0 (every_beat_ticks (bodometer (t + t + 2)))
              (by rw [(the_clock_folds_at_its_half t).2]
                  exact Nat.le_trans (Nat.le_succ (mtime (t + 1) + (t + t + 3) + 1)) hle')
            rw [(the_clock_folds_at_its_half t).2] at h
            exact h
          have h3 : T (mtime (t + 1) + 1) = t + 2 :=
            ih (t + 1) 0 (every_beat_ticks (bodometer (t + 1)))
              (Nat.le_trans
                (stack_left (mtime (t + 1)) 1 (t + t + 5) (Nat.le_add_left 1 (t + t + 4)))
                hle')
          rw [hM3]
          show T (mtime (t + 1) + (t + t + 3) + 3) = t + t + 4
          rw [the_tame_loop_closes_over_the_net (mtime (t + 1) + (t + t + 3)), h1, h2,
              show mtime (t + 1) + (t + t + 3) + 2 - (t + t + 4) = mtime (t + 1) + 1 from
                pull_out_the_middle (mtime (t + 1)) (t + t + 4) 1,
              show mtime (t + 1) + (t + t + 3) + 1 - (t + t + 3) = mtime (t + 1) + 1 from
                pull_out_the_middle (mtime (t + 1)) (t + t + 3) 1,
              h3]
          exact congrArg (· + 2) (carry_the_one t 2)
      | j' + 2, hj2 =>
          have hle' : mtime (t + 1) + (t + t + 4) + j' + 2 ≤ n := by
            have h := hle
            rw [hM3] at h
            exact Nat.le_of_succ_le_succ h
          have h1 : T (mtime (t + 1) + (t + t + 4) + j' + 2) = t + t + 4 := by
            have h := ih (t + t + 3) (j' + 1)
              (by rw [hb3]; exact Nat.le_trans (Nat.le_succ (j' + 2)) hj2)
              (by rw [hM3]; exact hle')
            rw [hM3] at h
            exact h
          have h2 : T (mtime (t + 1) + (t + t + 4) + j' + 1) = t + t + 4 := by
            have h := ih (t + t + 3) j'
              (by rw [hb3]
                  exact Nat.le_trans (Nat.le_succ (j' + 1))
                    (Nat.le_trans (Nat.le_succ (j' + 2)) hj2))
              (by rw [hM3]
                  exact Nat.le_trans (Nat.le_succ (mtime (t + 1) + (t + t + 4) + j' + 1)) hle')
            rw [hM3] at h
            exact h
          have hfloor : mtime (t + 1) + j' + 2 ≤ n :=
            Nat.le_trans
              (stack_right (mtime (t + 1) + j') (mtime (t + 1) + (t + t + 4) + j') 2
                (stack_right (mtime (t + 1)) (mtime (t + 1) + (t + t + 4)) j'
                  (Nat.le_add_right (mtime (t + 1)) (t + t + 4))))
              hle'
          have h3 : T (mtime (t + 1) + j' + 2) = t + 2 :=
            ih (t + 1) (j' + 1) (Nat.le_of_succ_le_succ hj2) hfloor
          have h4 : T (mtime (t + 1) + j' + 1) = t + 2 :=
            ih (t + 1) j'
              (Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_succ (j' + 2)) hj2))
              (Nat.le_trans (Nat.le_succ (mtime (t + 1) + j' + 1)) hfloor)
          rw [hM3]
          show T (mtime (t + 1) + (t + t + 4) + j' + 3) = t + t + 4
          rw [the_tame_loop_closes_over_the_net (mtime (t + 1) + (t + t + 4) + j'), h1, h2,
              show mtime (t + 1) + (t + t + 4) + j' + 2 - (t + t + 4)
                  = mtime (t + 1) + j' + 2 from
                pull_out_the_middle (mtime (t + 1)) (t + t + 4) (j' + 2),
              show mtime (t + 1) + (t + t + 4) + j' + 1 - (t + t + 4)
                  = mtime (t + 1) + j' + 1 from
                pull_out_the_middle (mtime (t + 1)) (t + t + 4) (j' + 1),
              h3, h4]
          exact congrArg (· + 2) (carry_the_one t 2)

theorem the_tame_walk_keeps_the_meter : ∀ (n : Nat), metered n
  | 0 => fun _ _ _ hle => absurd hle (Nat.not_succ_le_zero _)
  | n + 1 => metered_step n (the_tame_walk_keeps_the_meter n)

/-- info: 'Foam.Bridges.metered_step' does not depend on any axioms -/
#guard_msgs in #print axioms metered_step

/-- info: 'Foam.Bridges.the_tame_walk_keeps_the_meter' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_keeps_the_meter

theorem the_tame_walk_reads_the_binary_odometer (v j : Nat)
    (h : j < beat (bodometer v)) : T (mtime v + j + 1) = v + 1 :=
  the_tame_walk_keeps_the_meter (mtime v + j + 1) v j h (Nat.le_refl (mtime v + j + 1))

theorem a_new_count_reads_at_its_first_beat (v : Nat) : T (mtime v + 1) = v + 1 :=
  the_tame_walk_reads_the_binary_odometer v 0 (every_beat_ticks (bodometer v))

theorem the_walk_arrives_on_the_hour (v : Nat) : T (mtime (v + 1)) = v + 1 := by
  obtain ⟨c, hc⟩ := a_tick_is_a_step (beat (bodometer v)) (every_beat_ticks (bodometer v))
  show T (mtime v + beat (bodometer v)) = v + 1
  rw [hc]
  exact the_tame_walk_reads_the_binary_odometer v c (by rw [hc]; exact Nat.le_refl (c + 1))

theorem t_hums_the_hours :
    (T 2, T 5, T 6, T 10, T 11, T 13, T 14, T 19) = (1, 2, 3, 4, 5, 6, 7, 8) := rfl

/-- info: 'Foam.Bridges.the_tame_walk_reads_the_binary_odometer' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_reads_the_binary_odometer

/-- info: 'Foam.Bridges.a_new_count_reads_at_its_first_beat' does not depend on any axioms -/
#guard_msgs in #print axioms a_new_count_reads_at_its_first_beat

/-- info: 'Foam.Bridges.the_walk_arrives_on_the_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_arrives_on_the_hour

/-- info: 'Foam.Bridges.t_hums_the_hours' does not depend on any axioms -/
#guard_msgs in #print axioms t_hums_the_hours

theorem every_hour_strikes_some_count : ∀ (n : Nat),
    ∃ v j, j < beat (bodometer v) ∧ n + 1 = mtime v + j + 1
  | 0 => ⟨0, 0, Nat.le_succ 1, rfl⟩
  | n + 1 =>
      match every_hour_strikes_some_count n with
      | ⟨v, j, hj, he⟩ =>
          match a_tick_is_a_step (beat (bodometer v)) (every_beat_ticks (bodometer v)) with
          | ⟨c, hc⟩ =>
              match under_the_wire (j + 1) c (hc ▸ hj) with
              | Or.inl h =>
                  ⟨v, j + 1, by rw [hc]; exact Nat.succ_le_succ h, congrArg (· + 1) he⟩
              | Or.inr h =>
                  ⟨v + 1, 0, every_beat_ticks (bodometer (v + 1)),
                    (congrArg (· + 1) he).trans (by
                      show mtime v + j + 1 + 1 = mtime (v + 1) + 0 + 1
                      rw [Nat.succ.inj h]
                      show mtime v + c + 1 + 1 = mtime v + beat (bodometer v) + 0 + 1
                      rw [hc]
                      rfl)⟩

theorem the_clock_tells_the_whole_walk (n : Nat) :
    ∃ v, mtime v < n + 1 ∧ n + 1 ≤ mtime (v + 1) ∧ T (n + 1) = v + 1 := by
  obtain ⟨v, j, hj, he⟩ := every_hour_strikes_some_count n
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [he]
    exact Nat.succ_le_succ (Nat.le_add_right (mtime v) j)
  · rw [he]
    show mtime v + j + 1 ≤ mtime v + beat (bodometer v)
    exact stack_left (mtime v) (j + 1) (beat (bodometer v)) hj
  · rw [he]
    exact the_tame_walk_reads_the_binary_odometer v j hj

/-- info: 'Foam.Bridges.every_hour_strikes_some_count' does not depend on any axioms -/
#guard_msgs in #print axioms every_hour_strikes_some_count

/-- info: 'Foam.Bridges.the_clock_tells_the_whole_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_clock_tells_the_whole_walk

theorem the_shadow_beats_at_half_time (u j : Nat)
    (h : j < beat (bodometer (u + u + 1))) :
    slack (mtime (u + u + 1) + j + 1) = mtime u + j + 1 := by
  show mtime (u + u + 1) + j + 1 - T (mtime (u + u + 1) + j + 1) = mtime u + j + 1
  rw [the_tame_walk_reads_the_binary_odometer (u + u + 1) j h,
      (the_clock_folds_at_its_half u).1]
  show mtime u + (u + u + 2) + j + 1 - (u + u + 2) = mtime u + j + 1
  exact pull_out_the_middle (mtime u) (u + u + 2) (j + 1)

theorem the_tame_shadow_halves_an_odd_count (u j : Nat)
    (h : j < beat (bodometer u)) :
    T (slack (mtime (u + u + 1) + j + 1)) = u + 1 := by
  rw [the_shadow_beats_at_half_time u j
        (by rw [an_odd_count_lights_the_gate u]
            show j < beat (bodometer u) + 1
            exact Nat.le_trans h (Nat.le_succ (beat (bodometer u))))]
  exact the_tame_walk_reads_the_binary_odometer u j h

theorem the_tame_shadow_rounds_up_at_an_even_count (u : Nat) :
    T (slack (mtime (u + u + 2) + 1)) = u + 2 := by
  rw [show slack (mtime (u + u + 2) + 1) = mtime (u + 1) + 1 from by
        show mtime (u + u + 2) + 1 - T (mtime (u + u + 2) + 1) = mtime (u + 1) + 1
        rw [a_new_count_reads_at_its_first_beat (u + u + 2),
            (the_clock_folds_at_its_half u).2]
        show mtime (u + 1) + (u + u + 3) + 1 - (u + u + 3) = mtime (u + 1) + 1
        exact pull_out_the_middle (mtime (u + 1)) (u + u + 3) 1]
  exact a_new_count_reads_at_its_first_beat (u + 1)

/-- info: 'Foam.Bridges.the_shadow_beats_at_half_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_beats_at_half_time

/-- info: 'Foam.Bridges.the_tame_shadow_halves_an_odd_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_shadow_halves_an_odd_count

/-- info: 'Foam.Bridges.the_tame_shadow_rounds_up_at_an_even_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_shadow_rounds_up_at_an_even_count

theorem the_golden_staircase_holds_the_gnomon : Gnomon 1 fibN :=
  fun n => fibN_gnomon (n + 1)

theorem the_golden_staircase_holds_the_floor : Floored 1 fibN := fun k h =>
  match k, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, h => absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero k)

theorem worth_is_the_golden_price : ∀ (ds : List Bool) (i : Nat), worth i ds = price fibN i ds
  | [], _ => rfl
  | false :: rest, i => worth_is_the_golden_price rest (i + 1)
  | true :: rest, i => congrArg (fibN i + ·) (worth_is_the_golden_price rest (i + 1))

theorem the_golden_grammar_names_fibonacci (s : Nat → Nat)
    (hg : Gnomon 1 s) (hf : Floored 1 s) (n : Nat) : s (n + 1) = fibN (n + 1) :=
  the_grammar_names_its_staircase 1 s fibN hg hf
    the_golden_staircase_holds_the_gnomon the_golden_staircase_holds_the_floor n

theorem the_gate_is_the_unlit_lamp : ∀ (ds : List Bool), cleared 1 ds = !lit ds
  | [] => rfl
  | true :: _ => rfl
  | false :: _ => rfl

/-- info: 'Foam.Bridges.the_golden_staircase_holds_the_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_staircase_holds_the_gnomon

/-- info: 'Foam.Bridges.the_golden_staircase_holds_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_staircase_holds_the_floor

/-- info: 'Foam.Bridges.worth_is_the_golden_price' does not depend on any axioms -/
#guard_msgs in #print axioms worth_is_the_golden_price

/-- info: 'Foam.Bridges.the_golden_grammar_names_fibonacci' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_grammar_names_fibonacci

/-- info: 'Foam.Bridges.the_gate_is_the_unlit_lamp' does not depend on any axioms -/
#guard_msgs in #print axioms the_gate_is_the_unlit_lamp

theorem the_walker_reads_the_golden_page (n : Nat) : G n = price fibN 1 (odometer n) :=
  worth_is_the_golden_price (odometer n) 1

theorem the_drover_reads_the_herd_page (n : Nat) : H n = price herdN 2 (hodometer n) :=
  graze_is_the_herds_price (hodometer n) 2

theorem the_bodometer_reads_the_pegged_price (n : Nat) : price peg 1 (bodometer n) = n :=
  (gauge_is_the_rulers_price (bodometer n) 0).symm.trans (the_bodometer_reads_true n)

/-- info: 'Foam.Bridges.the_walker_reads_the_golden_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_reads_the_golden_page

/-- info: 'Foam.Bridges.the_drover_reads_the_herd_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_reads_the_herd_page

/-- info: 'Foam.Bridges.the_bodometer_reads_the_pegged_price' does not depend on any axioms -/
#guard_msgs in #print axioms the_bodometer_reads_the_pegged_price

def Registered (f : Nat → Nat) (s : Nat → Nat) (t : Nat) : Prop :=
  ∃ page : Nat → List Bool,
    (∀ n, price s (t + 2) (page n) = n) ∧ (∀ n, f n = price s (t + 1) (page n))

def Paged (f : Nat → Nat) : Prop :=
  ∃ e t : Nat, ∃ s : Nat → Nat, Gnomon e s ∧ Floored e s ∧ Registered f s t

theorem the_walker_is_registered : Registered G fibN 0 :=
  ⟨odometer,
    fun n => (worth_is_the_golden_price (odometer n) 2).symm.trans (the_odometer_reads_true n),
    fun n => worth_is_the_golden_price (odometer n) 1⟩

theorem the_drover_is_registered : Registered H herdN 1 :=
  ⟨hodometer,
    fun n => (graze_is_the_herds_price (hodometer n) 3).symm.trans (the_hodometer_reads_true n),
    fun n => graze_is_the_herds_price (hodometer n) 2⟩

theorem the_walker_reads_a_page : Paged G :=
  ⟨1, 0, fibN, the_golden_staircase_holds_the_gnomon, the_golden_staircase_holds_the_floor,
    the_walker_is_registered⟩

theorem the_drover_reads_a_page : Paged H :=
  ⟨2, 1, herdN, the_herd_holds_the_gnomon, the_herd_holds_the_floor,
    the_drover_is_registered⟩

/-- info: 'Foam.Bridges.the_walker_is_registered' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_is_registered

/-- info: 'Foam.Bridges.the_drover_is_registered' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_is_registered

/-- info: 'Foam.Bridges.the_walker_reads_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_reads_a_page

/-- info: 'Foam.Bridges.the_drover_reads_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_reads_a_page

theorem a_paged_walk_never_outruns_the_count (f : Nat → Nat) (hp : Paged f) (n : Nat) :
    f n ≤ n := by
  obtain ⟨e, t, s, hg, hf, page, hcount, hread⟩ := hp
  have h := the_lower_seat_reads_no_more e s hg hf (page n) t
  rw [hcount n] at h
  rw [hread n]
  exact h

theorem a_paged_walk_holds_the_half (f : Nat → Nat) (hp : Paged f) (n : Nat) :
    n ≤ f n + f n := by
  obtain ⟨e, t, s, hg, hf, page, hcount, hread⟩ := hp
  have h := the_higher_seat_reads_at_most_double e s hg hf (page n) t
  rw [hcount n] at h
  rw [hread n]
  exact h

theorem a_page_would_tame_the_wild_walk (hp : Paged Q) : Surefooted :=
  fun n => a_paged_walk_never_outruns_the_count Q hp (n + 1)

/-- info: 'Foam.Bridges.a_paged_walk_never_outruns_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms a_paged_walk_never_outruns_the_count

/-- info: 'Foam.Bridges.a_paged_walk_holds_the_half' does not depend on any axioms -/
#guard_msgs in #print axioms a_paged_walk_holds_the_half

/-- info: 'Foam.Bridges.a_page_would_tame_the_wild_walk' does not depend on any axioms -/
#guard_msgs in #print axioms a_page_would_tame_the_wild_walk

set_option maxRecDepth 4000 in
theorem the_wild_walk_undercuts_the_half : Q 49 = 24 := rfl

theorem the_wild_walk_reads_no_page : ¬ Paged Q := fun hp => by
  have h : (49 : Nat) ≤ Q 49 + Q 49 := a_paged_walk_holds_the_half Q hp 49
  rw [the_wild_walk_undercuts_the_half] at h
  exact absurd h (Nat.not_succ_le_self 48)

/-- info: 'Foam.Bridges.the_wild_walk_undercuts_the_half' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_undercuts_the_half

/-- info: 'Foam.Bridges.the_wild_walk_reads_no_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_reads_no_page

theorem the_ruler_reads_no_walk_in_space (f : Nat → Nat) (t : Nat) :
    ¬ Registered f peg t := fun hr => by
  obtain ⟨page, hcount, _⟩ := hr
  have h := the_high_pegs_read_in_twos (page 1) t
  rw [hcount 1] at h
  cases h with
  | inl h0 => exact nomatch h0
  | inr h2 => exact absurd (Nat.le_of_succ_le_succ h2) (Nat.not_succ_le_zero 0)

/-- info: 'Foam.Bridges.the_ruler_reads_no_walk_in_space' does not depend on any axioms -/
#guard_msgs in #print axioms the_ruler_reads_no_walk_in_space

def Clocked (f : Nat → Nat) : Prop :=
  ∃ c : Nat → Nat, c 0 = 0 ∧ (∀ v, c v < c (v + 1))
    ∧ (∀ v j, c v + j + 1 ≤ c (v + 1) → f (c v + j + 1) = v + 1)

theorem stack_free : ∀ (a b c : Nat), a + b ≤ a + c → b ≤ c
  | 0, b, c, h => by rw [Nat.zero_add b, Nat.zero_add c] at h; exact h
  | a + 1, b, c, h =>
      stack_free a b c (Nat.le_of_succ_le_succ (by
        rw [seat_shuffles a b, seat_shuffles a c] at h; exact h))

theorem the_tame_walk_is_clocked : Clocked T :=
  ⟨mtime, rfl, the_clock_never_stalls, fun v j h =>
    the_tame_walk_reads_the_binary_odometer v j
      (stack_free (mtime v) (j + 1) (beat (bodometer v)) h)⟩

/-- info: 'Foam.Bridges.stack_free' does not depend on any axioms -/
#guard_msgs in #print axioms stack_free

/-- info: 'Foam.Bridges.the_tame_walk_is_clocked' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_is_clocked

theorem a_clock_never_lags (c : Nat → Nat) (hs : ∀ v, c v < c (v + 1)) : ∀ v, v ≤ c v
  | 0 => Nat.zero_le (c 0)
  | v + 1 => Nat.le_trans (Nat.succ_le_succ (a_clock_never_lags c hs v)) (hs v)

theorem a_clock_never_slips (c : Nat → Nat) (hs : ∀ v, c v < c (v + 1)) :
    ∀ (b a : Nat), a ≤ b → c a ≤ c b
  | 0, 0, _ => Nat.le_refl (c 0)
  | 0, a + 1, h => absurd h (Nat.not_succ_le_zero a)
  | b + 1, a, h =>
      match under_the_wire a b h with
      | Or.inl h' =>
          Nat.le_trans (a_clock_never_slips c hs b a h')
            (Nat.le_trans (Nat.le_succ (c b)) (hs b))
      | Or.inr h' => by subst h'; exact Nat.le_refl (c (b + 1))

theorem a_clock_strikes_every_hour (c : Nat → Nat) (h0 : c 0 = 0)
    (hs : ∀ v, c v < c (v + 1)) :
    ∀ (n : Nat), ∃ v j, n + 1 = c v + j + 1 ∧ c v + j + 1 ≤ c (v + 1)
  | 0 => ⟨0, 0, by rw [h0], hs 0⟩
  | n + 1 =>
      match a_clock_strikes_every_hour c h0 hs n with
      | ⟨v, j, he, hle⟩ =>
          match under_the_wire (c v + j + 1 + 1) (c (v + 1)) (Nat.succ_le_succ hle) with
          | Or.inl h => ⟨v, j + 1, congrArg (· + 1) he, h⟩
          | Or.inr h => ⟨v + 1, 0, (congrArg (· + 1) he).trans h, hs (v + 1)⟩

/-- info: 'Foam.Bridges.a_clock_never_lags' does not depend on any axioms -/
#guard_msgs in #print axioms a_clock_never_lags

/-- info: 'Foam.Bridges.a_clock_never_slips' does not depend on any axioms -/
#guard_msgs in #print axioms a_clock_never_slips

/-- info: 'Foam.Bridges.a_clock_strikes_every_hour' does not depend on any axioms -/
#guard_msgs in #print axioms a_clock_strikes_every_hour

theorem a_clocked_walk_keeps_its_feet (f : Nat → Nat) (hc : Clocked f) (n : Nat) :
    f (n + 1) ≤ n + 1 := by
  obtain ⟨c, h0, hs, hr⟩ := hc
  obtain ⟨v, j, he, hle⟩ := a_clock_strikes_every_hour c h0 hs n
  rw [he, hr v j hle]
  exact Nat.succ_le_succ (Nat.le_trans (a_clock_never_lags c hs v) (Nat.le_add_right (c v) j))

theorem a_clocked_walk_never_steps_back (f : Nat → Nat) (hc : Clocked f) (n : Nat) :
    f (n + 1) ≤ f (n + 1 + 1) := by
  obtain ⟨c, h0, hs, hr⟩ := hc
  obtain ⟨v, j, he, hle⟩ := a_clock_strikes_every_hour c h0 hs n
  obtain ⟨w, i, he', hle'⟩ := a_clock_strikes_every_hour c h0 hs (n + 1)
  rw [he', he, hr v j hle, hr w i hle']
  cases Nat.lt_or_ge v w with
  | inl hvw => exact Nat.succ_le_succ (Nat.le_trans (Nat.le_succ v) hvw)
  | inr hwv =>
      cases at_the_rail w v hwv with
      | inr heq => rw [heq]; exact Nat.le_refl (v + 1)
      | inl hlt =>
          have hcw : c (w + 1) ≤ c v := a_clock_never_slips c hs v (w + 1) hlt
          have hup : n + 1 + 1 ≤ c (w + 1) := by rw [he']; exact hle'
          have hdn : c v ≤ n := by rw [Nat.succ.inj he]; exact Nat.le_add_right (c v) j
          have habs : n + 1 + 1 ≤ n := Nat.le_trans hup (Nat.le_trans hcw hdn)
          exact absurd (Nat.le_trans (Nat.le_succ (n + 1)) habs) (Nat.not_succ_le_self n)

theorem a_clock_would_tame_the_wild_walk (hc : Clocked Q) : Surefooted :=
  fun n => a_clocked_walk_keeps_its_feet Q hc n

theorem the_wild_walk_reads_no_clock : ¬ Clocked Q := fun hc => by
  have h : Q 15 ≤ Q 16 := a_clocked_walk_never_steps_back Q hc 14
  rw [← the_wild_walk_steps_back] at h
  exact absurd h (Nat.not_succ_le_self (Q 16))

/-- info: 'Foam.Bridges.a_clocked_walk_keeps_its_feet' does not depend on any axioms -/
#guard_msgs in #print axioms a_clocked_walk_keeps_its_feet

/-- info: 'Foam.Bridges.a_clocked_walk_never_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms a_clocked_walk_never_steps_back

/-- info: 'Foam.Bridges.a_clock_would_tame_the_wild_walk' does not depend on any axioms -/
#guard_msgs in #print axioms a_clock_would_tame_the_wild_walk

/-- info: 'Foam.Bridges.the_wild_walk_reads_no_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_reads_no_clock

theorem three_walks_one_grammar : Paged G ∧ Paged H ∧ Clocked T :=
  ⟨the_walker_reads_a_page, the_drover_reads_a_page, the_tame_walk_is_clocked⟩

theorem the_wild_walk_reads_alone : ¬ Paged Q ∧ ¬ Clocked Q :=
  ⟨the_wild_walk_reads_no_page, the_wild_walk_reads_no_clock⟩

/-- info: 'Foam.Bridges.three_walks_one_grammar' does not depend on any axioms -/
#guard_msgs in #print axioms three_walks_one_grammar

/-- info: 'Foam.Bridges.the_wild_walk_reads_alone' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_reads_alone

def look : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, i + 1 => look rest i

def traceNet : Net where
  Page := List Nat
  Seat := Nat
  Ans := Nat
  read? := fun qs i => look qs i
  mend := fun _ => 1

theorem the_net_answers_the_peek : ∀ (qs : List Nat) (i : Nat),
    answer traceNet qs i = peek qs i
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, i + 1 => the_net_answers_the_peek rest i

theorem the_wild_walk_was_born_on_the_net (n : Nat) :
    Q n = answer traceNet (qtrace n) (0 : Nat) :=
  (the_net_answers_the_peek (qtrace n) 0).symm

theorem the_tame_walk_was_born_on_the_net (n : Nat) :
    T n = answer traceNet (ttrace n) (0 : Nat) :=
  (the_net_answers_the_peek (ttrace n) 0).symm

theorem the_mend_is_the_floor : traceNet.mend (0 : Nat) = Q 0 ∧ traceNet.mend (0 : Nat) = T 0 :=
  ⟨rfl, rfl⟩

/-- info: 'Foam.Bridges.the_net_answers_the_peek' does not depend on any axioms -/
#guard_msgs in #print axioms the_net_answers_the_peek

/-- info: 'Foam.Bridges.the_wild_walk_was_born_on_the_net' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_was_born_on_the_net

/-- info: 'Foam.Bridges.the_tame_walk_was_born_on_the_net' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_was_born_on_the_net

/-- info: 'Foam.Bridges.the_mend_is_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_mend_is_the_floor

theorem the_trace_fills_its_page : ∀ (n : Nat), (qtrace n).length = n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => congrArg (· + 1) (the_trace_fills_its_page (n + 2))

theorem the_tame_trace_fills_its_page : ∀ (n : Nat), (ttrace n).length = n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => congrArg (· + 1) (the_tame_trace_fills_its_page (n + 2))

theorem look_finds_the_page : ∀ (qs : List Nat) (i : Nat),
    i + 1 ≤ qs.length → ∃ a, look qs i = some a
  | [], i, h => absurd h (Nat.not_succ_le_zero i)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: rest, i + 1, h => look_finds_the_page rest i (Nat.le_of_succ_le_succ h)

/-- info: 'Foam.Bridges.the_trace_fills_its_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_trace_fills_its_page

/-- info: 'Foam.Bridges.the_tame_trace_fills_its_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_trace_fills_its_page

/-- info: 'Foam.Bridges.look_finds_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms look_finds_the_page

theorem sure_feet_never_touch_the_net (hs : Surefooted) (n : Nat) :
    ¬ Consults traceNet (qtrace (n + 2)) (Q (n + 2) - 1)
      ∧ ¬ Consults traceNet (qtrace (n + 2)) (Q (n + 1) - 1) := by
  constructor
  · intro hc
    have hb : Q (n + 2) - 1 + 1 ≤ (qtrace (n + 2)).length := by
      rw [the_trace_fills_its_page (n + 2),
          sub_one_back (Q (n + 2)) (the_wild_walk_glows (n + 2))]
      exact hs (n + 1)
    obtain ⟨a, ha⟩ := look_finds_the_page (qtrace (n + 2)) (Q (n + 2) - 1) hb
    exact nomatch (ha.symm.trans hc)
  · intro hc
    have hb : Q (n + 1) - 1 + 1 ≤ (qtrace (n + 2)).length := by
      rw [the_trace_fills_its_page (n + 2),
          sub_one_back (Q (n + 1)) (the_wild_walk_glows (n + 1))]
      exact Nat.le_trans (hs n) (Nat.le_succ (n + 1))
    obtain ⟨a, ha⟩ := look_finds_the_page (qtrace (n + 2)) (Q (n + 1) - 1) hb
    exact nomatch (ha.symm.trans hc)

theorem the_tame_walk_touches_the_net_at_the_floor :
    Consults traceNet (ttrace 2) (T 1 + 1) := rfl

theorem the_tame_walk_never_touches_the_net_again (n : Nat) :
    ¬ Consults traceNet (ttrace (n + 3)) (T (n + 3))
      ∧ ¬ Consults traceNet (ttrace (n + 3)) (T (n + 2) + 1) := by
  constructor
  · intro hc
    have hb : T (n + 3) + 1 ≤ (ttrace (n + 3)).length := by
      rw [the_tame_trace_fills_its_page (n + 3)]
      exact Nat.succ_le_succ (the_tame_walk_stays_a_step_behind (n + 1))
    obtain ⟨a, ha⟩ := look_finds_the_page (ttrace (n + 3)) (T (n + 3)) hb
    exact nomatch (ha.symm.trans hc)
  · intro hc
    have hb : T (n + 2) + 1 + 1 ≤ (ttrace (n + 3)).length := by
      rw [the_tame_trace_fills_its_page (n + 3)]
      exact Nat.succ_le_succ (Nat.succ_le_succ (the_tame_walk_stays_a_step_behind n))
    obtain ⟨a, ha⟩ := look_finds_the_page (ttrace (n + 3)) (T (n + 2) + 1) hb
    exact nomatch (ha.symm.trans hc)

/-- info: 'Foam.Bridges.sure_feet_never_touch_the_net' does not depend on any axioms -/
#guard_msgs in #print axioms sure_feet_never_touch_the_net

/-- info: 'Foam.Bridges.the_tame_walk_touches_the_net_at_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_touches_the_net_at_the_floor

/-- info: 'Foam.Bridges.the_tame_walk_never_touches_the_net_again' does not depend on any axioms -/
#guard_msgs in #print axioms the_tame_walk_never_touches_the_net_again

theorem two_holes_one_mending :
    (Nonempty (NetHom planeNet (mended planeNet)) ∧ Whole (mended planeNet))
      ∧ (Nonempty (NetHom traceNet (mended traceNet)) ∧ Whole (mended traceNet)) :=
  ⟨⟨⟨the_mending planeNet⟩, the_mended_page_has_no_holes planeNet⟩,
    ⟨⟨the_mending traceNet⟩, the_mended_page_has_no_holes traceNet⟩⟩

/-- info: 'Foam.Bridges.two_holes_one_mending' does not depend on any axioms -/
#guard_msgs in #print axioms two_holes_one_mending

def upshift (ds : List Bool) : List Bool := false :: ds

theorem the_downshift_undoes_the_upshift (ds : List Bool) :
    downshift (upshift ds) = ds := rfl

theorem the_hdownshift_undoes_the_upshift (ds : List Bool) :
    hdownshift (upshift ds) = ds := rfl

theorem the_upshift_reads_one_seat_up (ds : List Bool) (i : Nat) :
    worth i (upshift ds) = worth (i + 1) ds := rfl

theorem the_upshift_grazes_one_seat_up (ds : List Bool) (i : Nat) :
    graze i (upshift ds) = graze (i + 1) ds := rfl

theorem the_upshift_keeps_the_cap : ∀ (ds : List Bool), ds ≠ [] → capped ds = true →
    capped (upshift ds) = true
  | [], hne, _ => absurd rfl hne
  | d :: rest, _, hc => (capped_step false d rest).trans hc

/-- info: 'Foam.Bridges.the_downshift_undoes_the_upshift' does not depend on any axioms -/
#guard_msgs in #print axioms the_downshift_undoes_the_upshift

/-- info: 'Foam.Bridges.the_hdownshift_undoes_the_upshift' does not depend on any axioms -/
#guard_msgs in #print axioms the_hdownshift_undoes_the_upshift

/-- info: 'Foam.Bridges.the_upshift_reads_one_seat_up' does not depend on any axioms -/
#guard_msgs in #print axioms the_upshift_reads_one_seat_up

/-- info: 'Foam.Bridges.the_upshift_grazes_one_seat_up' does not depend on any axioms -/
#guard_msgs in #print axioms the_upshift_grazes_one_seat_up

/-- info: 'Foam.Bridges.the_upshift_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_upshift_keeps_the_cap

theorem click_never_blanks : ∀ (ds : List Bool), click ds ≠ []
  | [] => fun h => nomatch h
  | false :: rest => carry_never_blanks (false :: rest)
  | true :: _ => fun h => nomatch h

theorem hclick_never_blanks : ∀ (ds : List Bool), hclick ds ≠ []
  | [] => fun h => nomatch h
  | [false] => fun h => nomatch h
  | false :: false :: rest => hcarry_never_blanks (false :: false :: rest)
  | false :: true :: _ => fun h => nomatch h
  | true :: _ => fun h => nomatch h

/-- info: 'Foam.Bridges.click_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms click_never_blanks

/-- info: 'Foam.Bridges.hclick_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_never_blanks

def gtime (v : Nat) : Nat := worth 3 (odometer v)

theorem the_golden_clock_hums :
    (gtime 0, gtime 1, gtime 2, gtime 3, gtime 4, gtime 5, gtime 6, gtime 7)
      = (0, 2, 3, 5, 7, 8, 10, 11) := rfl

theorem the_golden_clock_adds_the_shadow (v : Nat) : gtime v = v + G v :=
  (worth_gnomon (odometer v) 1).trans
    (congrArg (· + G v) (the_odometer_reads_true v))

/-- info: 'Foam.Bridges.the_golden_clock_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_clock_hums

/-- info: 'Foam.Bridges.the_golden_clock_adds_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_clock_adds_the_shadow

theorem the_golden_hour_writes_the_page_above (n : Nat) :
    odometer (gtime (n + 1)) = upshift (odometer (n + 1)) :=
  (the_odometer_is_the_only_spaced_page (gtime (n + 1)) (upshift (odometer (n + 1)))
    (noconsec_false_cons (the_odometer_spaces (n + 1)))
    (the_upshift_keeps_the_cap (odometer (n + 1)) (click_never_blanks (odometer n))
      (the_odometer_wastes_no_seats (n + 1)))
    rfl).symm

theorem the_golden_hour_rests_the_gate : ∀ (v : Nat), lit (odometer (gtime v)) = false
  | 0 => rfl
  | v + 1 => by rw [the_golden_hour_writes_the_page_above v]; rfl

theorem the_walker_arrives_on_the_hour : ∀ (v : Nat), G (gtime v) = v
  | 0 => rfl
  | v + 1 => by
      show worth 1 (odometer (gtime (v + 1))) = v + 1
      rw [the_golden_hour_writes_the_page_above v]
      exact the_odometer_reads_true (v + 1)

theorem a_new_count_walks_at_its_first_beat (v : Nat) : G (gtime v + 1) = v + 1 := by
  show worth 1 (click (odometer (gtime v))) = v + 1
  rw [click_moves_the_shadow (odometer (gtime v)) (the_odometer_spaces (gtime v))
        (the_golden_hour_rests_the_gate v)]
  exact congrArg (· + 1) (the_walker_arrives_on_the_hour v)

/-- info: 'Foam.Bridges.the_golden_hour_writes_the_page_above' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_hour_writes_the_page_above

/-- info: 'Foam.Bridges.the_golden_hour_rests_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_hour_rests_the_gate

/-- info: 'Foam.Bridges.the_walker_arrives_on_the_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_arrives_on_the_hour

/-- info: 'Foam.Bridges.a_new_count_walks_at_its_first_beat' does not depend on any axioms -/
#guard_msgs in #print axioms a_new_count_walks_at_its_first_beat

theorem the_golden_beat_reads_the_lamp (v : Nat) :
    gtime (v + 1) = gtime v + cond (lit (odometer v)) 1 2 := by
  cases hl : lit (odometer v) with
  | true =>
      have hstep : G (v + 1) = G v :=
        click_holds_the_shadow (odometer v) (the_odometer_spaces v) hl
      show gtime (v + 1) = gtime v + 1
      rw [the_golden_clock_adds_the_shadow (v + 1), the_golden_clock_adds_the_shadow v,
          hstep]
      exact seat_shuffles v (G v)
  | false =>
      have hstep : G (v + 1) = G v + 1 :=
        click_moves_the_shadow (odometer v) (the_odometer_spaces v) hl
      show gtime (v + 1) = gtime v + 2
      rw [the_golden_clock_adds_the_shadow (v + 1), the_golden_clock_adds_the_shadow v,
          hstep]
      exact (Nat.add_assoc (v + 1) (G v) 1).symm.trans
        (congrArg (· + 1) (seat_shuffles v (G v)))

theorem the_golden_beat_reads_the_gate (v : Nat) :
    gtime (v + 1) = gtime v + cond (cleared 1 (odometer v)) 2 1 := by
  rw [the_gate_is_the_unlit_lamp (odometer v), the_golden_beat_reads_the_lamp v]
  cases lit (odometer v) with
  | false => exact rfl
  | true => exact rfl

theorem the_golden_clock_never_stalls (v : Nat) : gtime v < gtime (v + 1) := by
  rw [the_golden_beat_reads_the_lamp v]
  cases lit (odometer v) with
  | false => exact Nat.le_succ (gtime v + 1)
  | true => exact Nat.le_refl (gtime v + 1)

theorem the_golden_clock_never_leaps (v : Nat) : gtime (v + 1) ≤ gtime v + 2 := by
  rw [the_golden_beat_reads_the_lamp v]
  cases lit (odometer v) with
  | false => exact Nat.le_refl (gtime v + 2)
  | true => exact Nat.add_le_add_left (Nat.le_succ 1) (gtime v)

/-- info: 'Foam.Bridges.the_golden_beat_reads_the_lamp' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_beat_reads_the_lamp

/-- info: 'Foam.Bridges.the_golden_beat_reads_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_beat_reads_the_gate

/-- info: 'Foam.Bridges.the_golden_clock_never_stalls' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_clock_never_stalls

/-- info: 'Foam.Bridges.the_golden_clock_never_leaps' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_clock_never_leaps

theorem the_walker_reads_the_golden_hours :
    ∀ (v j : Nat), gtime v + j + 1 ≤ gtime (v + 1) → G (gtime v + j + 1) = v + 1
  | v, 0, _ => a_new_count_walks_at_its_first_beat v
  | v, 1, h => by
      have heq : gtime (v + 1) = gtime v + 2 :=
        Nat.le_antisymm (the_golden_clock_never_leaps v) h
      rw [show gtime v + 1 + 1 = gtime (v + 1) from heq.symm]
      exact the_walker_arrives_on_the_hour (v + 1)
  | v, j + 2, h => by
      have hle : gtime v + (j + 3) ≤ gtime v + 2 :=
        Nat.le_trans h (the_golden_clock_never_leaps v)
      exact absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
        (stack_free (gtime v) (j + 3) 2 hle))) (Nat.not_succ_le_zero j)

theorem the_walker_is_clocked : Clocked G :=
  ⟨gtime, rfl, the_golden_clock_never_stalls, the_walker_reads_the_golden_hours⟩

/-- info: 'Foam.Bridges.the_walker_reads_the_golden_hours' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_reads_the_golden_hours

/-- info: 'Foam.Bridges.the_walker_is_clocked' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_is_clocked

def htime (v : Nat) : Nat := graze 4 (hodometer v)

theorem the_herd_clock_hums :
    (htime 0, htime 1, htime 2, htime 3, htime 4, htime 5, htime 6, htime 7)
      = (0, 2, 3, 4, 6, 8, 9, 11) := rfl

theorem the_herd_clock_adds_the_second_shadow (v : Nat) : htime v = v + H (H v) := by
  show graze 4 (hodometer v) = v + H (H v)
  rw [the_second_shadow_reads_one_down v]
  exact (graze_gnomon (hodometer v) 1).trans
    (congrArg (· + graze 1 (hodometer v)) (the_hodometer_reads_true v))

/-- info: 'Foam.Bridges.the_herd_clock_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_clock_hums

/-- info: 'Foam.Bridges.the_herd_clock_adds_the_second_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_clock_adds_the_second_shadow

theorem hclick_moves_the_second_shadow : ∀ (ds : List Bool), Sparse ds →
    clearing ds = true → graze 1 (hclick ds) = graze 1 ds + 1
  | [], _, _ => rfl
  | [false], _, _ => rfl
  | true :: _, _, hcl => nomatch hcl
  | false :: true :: _, _, hcl => nomatch hcl
  | false :: false :: rest, h, _ => by
      show graze 1 (hcarry (false :: false :: rest)) = graze 1 (false :: false :: rest) + 1
      rw [hcarry_pays (false :: false :: rest) 1 h rfl]
      exact Nat.add_comm 1 (graze 1 (false :: false :: rest))

theorem hclick_holds_the_second_shadow : ∀ (ds : List Bool), Sparse ds →
    clearing ds = false → graze 1 (hclick ds) = graze 1 ds
  | [], _, hcl => nomatch hcl
  | [false], _, hcl => nomatch hcl
  | false :: false :: _, _, hcl => nomatch hcl
  | true :: rest, h, _ => by
      show graze 2 (hcarry rest) = herdN 1 + graze 2 rest
      rw [hcarry_pays rest 2 (sparse_tail h) (sparse_head h)]
      rfl
  | false :: true :: rest, h, _ => by
      show graze 3 (hcarry rest) = herdN 2 + graze 3 rest
      rw [hcarry_pays rest 3 (sparse_tail (sparse_tail h)) (sparse_head (sparse_tail h))]
      rfl

/-- info: 'Foam.Bridges.hclick_moves_the_second_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_moves_the_second_shadow

/-- info: 'Foam.Bridges.hclick_holds_the_second_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms hclick_holds_the_second_shadow

theorem the_herd_hour_writes_the_page_above (n : Nat) :
    hodometer (htime (n + 1)) = upshift (hodometer (n + 1)) :=
  (the_hodometer_is_the_only_sparse_page (htime (n + 1)) (upshift (hodometer (n + 1)))
    (the_hodometer_spaces (n + 1))
    (the_upshift_keeps_the_cap (hodometer (n + 1)) (hclick_never_blanks (hodometer n))
      (the_hodometer_wastes_no_seats (n + 1)))
    rfl).symm

theorem the_herd_hour_rests_the_gate : ∀ (v : Nat), lit (hodometer (htime v)) = false
  | 0 => rfl
  | v + 1 => by rw [the_herd_hour_writes_the_page_above v]; rfl

theorem the_drover_arrives_on_the_hour : ∀ (v : Nat), H (htime v) = v
  | 0 => rfl
  | v + 1 => by
      show graze 2 (hodometer (htime (v + 1))) = v + 1
      rw [the_herd_hour_writes_the_page_above v]
      exact the_hodometer_reads_true (v + 1)

theorem a_new_count_herds_at_its_first_beat (v : Nat) : H (htime v + 1) = v + 1 := by
  show graze 2 (hclick (hodometer (htime v))) = v + 1
  rw [hclick_moves_the_shadow (hodometer (htime v)) (the_hodometer_spaces (htime v))
        (the_herd_hour_rests_the_gate v)]
  exact congrArg (· + 1) (the_drover_arrives_on_the_hour v)

/-- info: 'Foam.Bridges.the_herd_hour_writes_the_page_above' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_hour_writes_the_page_above

/-- info: 'Foam.Bridges.the_herd_hour_rests_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_hour_rests_the_gate

/-- info: 'Foam.Bridges.the_drover_arrives_on_the_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_arrives_on_the_hour

/-- info: 'Foam.Bridges.a_new_count_herds_at_its_first_beat' does not depend on any axioms -/
#guard_msgs in #print axioms a_new_count_herds_at_its_first_beat

theorem the_herd_beat_reads_the_clearing (v : Nat) :
    htime (v + 1) = htime v + cond (clearing (hodometer v)) 2 1 := by
  cases hcl : clearing (hodometer v) with
  | true =>
      have hstep : H (H (v + 1)) = H (H v) + 1 := by
        rw [the_second_shadow_reads_one_down (v + 1), the_second_shadow_reads_one_down v]
        exact hclick_moves_the_second_shadow (hodometer v) (the_hodometer_spaces v) hcl
      show htime (v + 1) = htime v + 2
      rw [the_herd_clock_adds_the_second_shadow (v + 1),
          the_herd_clock_adds_the_second_shadow v, hstep]
      exact (Nat.add_assoc (v + 1) (H (H v)) 1).symm.trans
        (congrArg (· + 1) (seat_shuffles v (H (H v))))
  | false =>
      have hstep : H (H (v + 1)) = H (H v) := by
        rw [the_second_shadow_reads_one_down (v + 1), the_second_shadow_reads_one_down v]
        exact hclick_holds_the_second_shadow (hodometer v) (the_hodometer_spaces v) hcl
      show htime (v + 1) = htime v + 1
      rw [the_herd_clock_adds_the_second_shadow (v + 1),
          the_herd_clock_adds_the_second_shadow v, hstep]
      exact seat_shuffles v (H (H v))

theorem the_herd_beat_reads_the_gate (v : Nat) :
    htime (v + 1) = htime v + cond (cleared 2 (hodometer v)) 2 1 := by
  rw [← the_clearing_is_two_seats (hodometer v)]
  exact the_herd_beat_reads_the_clearing v

theorem the_herd_clock_never_stalls (v : Nat) : htime v < htime (v + 1) := by
  rw [the_herd_beat_reads_the_clearing v]
  cases clearing (hodometer v) with
  | false => exact Nat.le_refl (htime v + 1)
  | true => exact Nat.le_succ (htime v + 1)

theorem the_herd_clock_never_leaps (v : Nat) : htime (v + 1) ≤ htime v + 2 := by
  rw [the_herd_beat_reads_the_clearing v]
  cases clearing (hodometer v) with
  | false => exact Nat.add_le_add_left (Nat.le_succ 1) (htime v)
  | true => exact Nat.le_refl (htime v + 2)

/-- info: 'Foam.Bridges.the_herd_beat_reads_the_clearing' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_beat_reads_the_clearing

/-- info: 'Foam.Bridges.the_herd_beat_reads_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_beat_reads_the_gate

/-- info: 'Foam.Bridges.the_herd_clock_never_stalls' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_clock_never_stalls

/-- info: 'Foam.Bridges.the_herd_clock_never_leaps' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_clock_never_leaps

theorem the_drover_reads_the_herd_hours :
    ∀ (v j : Nat), htime v + j + 1 ≤ htime (v + 1) → H (htime v + j + 1) = v + 1
  | v, 0, _ => a_new_count_herds_at_its_first_beat v
  | v, 1, h => by
      have heq : htime (v + 1) = htime v + 2 :=
        Nat.le_antisymm (the_herd_clock_never_leaps v) h
      rw [show htime v + 1 + 1 = htime (v + 1) from heq.symm]
      exact the_drover_arrives_on_the_hour (v + 1)
  | v, j + 2, h => by
      have hle : htime v + (j + 3) ≤ htime v + 2 :=
        Nat.le_trans h (the_herd_clock_never_leaps v)
      exact absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
        (stack_free (htime v) (j + 3) 2 hle))) (Nat.not_succ_le_zero j)

theorem the_drover_is_clocked : Clocked H :=
  ⟨htime, rfl, the_herd_clock_never_stalls, the_drover_reads_the_herd_hours⟩

/-- info: 'Foam.Bridges.the_drover_reads_the_herd_hours' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_reads_the_herd_hours

/-- info: 'Foam.Bridges.the_drover_is_clocked' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_is_clocked

theorem the_walker_reads_in_both_modes : Paged G ∧ Clocked G :=
  ⟨the_walker_reads_a_page, the_walker_is_clocked⟩

theorem the_drover_reads_in_both_modes : Paged H ∧ Clocked H :=
  ⟨the_drover_reads_a_page, the_drover_is_clocked⟩

theorem every_tame_walk_reads_in_time : Clocked G ∧ Clocked H ∧ Clocked T :=
  ⟨the_walker_is_clocked, the_drover_is_clocked, the_tame_walk_is_clocked⟩

theorem the_family_meets_in_time :
    (Clocked G ∧ Clocked H ∧ Clocked T) ∧ ¬ Clocked Q :=
  ⟨every_tame_walk_reads_in_time, the_wild_walk_reads_no_clock⟩

/-- info: 'Foam.Bridges.the_walker_reads_in_both_modes' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_reads_in_both_modes

/-- info: 'Foam.Bridges.the_drover_reads_in_both_modes' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_reads_in_both_modes

/-- info: 'Foam.Bridges.every_tame_walk_reads_in_time' does not depend on any axioms -/
#guard_msgs in #print axioms every_tame_walk_reads_in_time

/-- info: 'Foam.Bridges.the_family_meets_in_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_meets_in_time

def coil (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | j + 1, x => coil f j (f x)

def W (s : Nat → Nat) (e n : Nat) : Nat := assay s e (crank e n)

def slip (e : Nat) : List Nat → List Nat
  | [] => []
  | 0 :: gs => perch e gs
  | (g + 1) :: gs => g :: gs

def stime (s : Nat → Nat) (e v : Nat) : Nat := assay s (e + 2) (crank e v)

theorem gnomon_tn (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s) (n : Nat) :
    s (t + n + 3) = s (t + n + 2) + s (n + 1) := by
  have h : s (n + t + 3) = s (n + t + 2) + s (n + 1) := hg n
  rw [Nat.add_comm t n]
  exact h

/-- info: 'Foam.Bridges.gnomon_tn' does not depend on any axioms -/
#guard_msgs in #print axioms gnomon_tn

theorem slip_tick_lit (t : Nat) : ∀ (gs : List Nat), afoot gs = true →
    slip (t + 1) (tick (t + 1) gs) = slip (t + 1) gs
  | [], h => nomatch h
  | (_ + 1) :: _, h => nomatch h
  | 0 :: gs, _ => by
      show slip (t + 1) (lift 1 (perch (t + 1) gs)) = perch (t + 1) gs
      cases hp : perch (t + 1) gs with
      | nil => exact absurd hp (the_perch_never_blanks (t + 1) gs)
      | cons h hs => rfl

theorem slip_tick_unlit (t : Nat) : ∀ (gs : List Nat), afoot gs = false →
    slip (t + 1) (tick (t + 1) gs) = tick (t + 1) (slip (t + 1) gs)
  | [], _ => rfl
  | 0 :: _, h => nomatch h
  | (g + 1) :: gs, _ => by
      cases hb : Nat.ble (t + 1) g with
      | true =>
          have hble : Nat.ble (t + 1) (g + 1) = true :=
            Nat.ble_eq_true_of_le (Nat.le_succ_of_le (Nat.le_of_ble_eq_true hb))
          have hbeq : Nat.beq (g + 1) (t + 1) = false := by
            cases hb2 : Nat.beq (g + 1) (t + 1) with
            | false => rfl
            | true =>
                have hgt : g = t := Nat.succ.inj (Nat.eq_of_beq_eq_true hb2)
                subst hgt
                exact absurd (Nat.le_of_ble_eq_true hb) (Nat.not_succ_le_self g)
          show slip (t + 1) (cond (Nat.ble (t + 1) (g + 1)) (perch (t + 1) ((g + 1) :: gs))
              (lift (g + 1 + 1) (perch (t + 1) gs)))
            = cond (Nat.ble (t + 1) g) (perch (t + 1) (g :: gs)) (lift (g + 1) (perch (t + 1) gs))
          rw [hble, hb]
          show slip (t + 1) (cond (Nat.beq (g + 1) (t + 1)) (lift (t + 1 + 1) (perch (t + 1) gs))
              (0 :: (g + 1 - 1) :: gs))
            = perch (t + 1) (g :: gs)
          rw [hbeq]
          rfl
      | false =>
          have hlt : g + 1 ≤ t + 1 := ble_shuts (t + 1) g hb
          cases at_the_rail (g + 1) (t + 1) hlt with
          | inr heq =>
              have hgt : g = t := Nat.succ.inj heq
              subst hgt
              show slip (g + 1) (cond (Nat.ble (g + 1) (g + 1)) (perch (g + 1) ((g + 1) :: gs))
                  (lift (g + 1 + 1) (perch (g + 1) gs)))
                = cond (Nat.ble (g + 1) g) (perch (g + 1) (g :: gs))
                    (lift (g + 1) (perch (g + 1) gs))
              rw [ble_mirrors (g + 1), ble_steps_back g]
              show slip (g + 1) (cond (Nat.beq (g + 1) (g + 1)) (lift (g + 1 + 1) (perch (g + 1) gs))
                  (0 :: (g + 1 - 1) :: gs))
                = lift (g + 1) (perch (g + 1) gs)
              rw [beq_mirrors (g + 1)]
              cases hp : perch (g + 1) gs with
              | nil => exact absurd hp (the_perch_never_blanks (g + 1) gs)
              | cons h hs => rfl
          | inl hlt2 =>
              have hble1 : Nat.ble (t + 1) (g + 1) = false := ble_shuts_high (g + 1) (t + 1) hlt2
              show slip (t + 1) (cond (Nat.ble (t + 1) (g + 1)) (perch (t + 1) ((g + 1) :: gs))
                  (lift (g + 1 + 1) (perch (t + 1) gs)))
                = cond (Nat.ble (t + 1) g) (perch (t + 1) (g :: gs))
                    (lift (g + 1) (perch (t + 1) gs))
              rw [hble1, hb]
              cases hp : perch (t + 1) gs with
              | nil => exact absurd hp (the_perch_never_blanks (t + 1) gs)
              | cons h hs => rfl

/-- info: 'Foam.Bridges.slip_tick_lit' does not depend on any axioms -/
#guard_msgs in #print axioms slip_tick_lit

/-- info: 'Foam.Bridges.slip_tick_unlit' does not depend on any axioms -/
#guard_msgs in #print axioms slip_tick_unlit

theorem the_family_holds_the_shadow (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (gs : List Nat), Spread (t + 1) gs → afoot gs = true →
      assay s (t + 1) (tick (t + 1) gs) = assay s (t + 1) gs
  | [], _, hl => nomatch hl
  | (_ + 1) :: _, _, hl => nomatch hl
  | 0 :: gs, hs, _ => by
      show assay s (t + 1) (lift 1 (perch (t + 1) gs)) = assay s (t + 1) (0 :: gs)
      rw [the_lift_reads_above s (perch (t + 1) gs) (t + 1) 1]
      rw [the_perch_pays (t + 1) s hg gs (t + 1) hs]
      show s (t + 1 + 1) + assay s (t + 1 + 1) gs = s (t + 1) + assay s (t + 1 + 1) gs
      have hf2 : s (t + 1 + 1) = 1 := hf (t + 1) (Nat.le_refl (t + 1))
      have hf1 : s (t + 1) = 1 := hf t (Nat.le_succ t)
      rw [hf2, hf1]

theorem the_family_moves_the_shadow (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (gs : List Nat), Spread (t + 1) gs → afoot gs = false →
      assay s (t + 1) (tick (t + 1) gs) = assay s (t + 1) gs + 1
  | [], _, _ => by
      show s (t + 1) + 0 = 0 + 1
      rw [hf t (Nat.le_succ t)]
  | 0 :: _, _, hl => nomatch hl
  | (g + 1) :: gs, hs, _ => by
      show assay s (t + 1) (cond (Nat.ble (t + 1) (g + 1)) (perch (t + 1) ((g + 1) :: gs))
          (lift (g + 1 + 1) (perch (t + 1) gs)))
        = assay s (t + 1) ((g + 1) :: gs) + 1
      cases hb : Nat.ble (t + 1) (g + 1) with
      | true =>
          show assay s (t + 1) (perch (t + 1) ((g + 1) :: gs))
            = assay s (t + 1) ((g + 1) :: gs) + 1
          rw [the_perch_pays (t + 1) s hg ((g + 1) :: gs) t ⟨Nat.le_of_ble_eq_true hb, hs⟩]
          rw [hf t (Nat.le_succ t)]
          exact Nat.add_comm 1 (assay s (t + 1) ((g + 1) :: gs))
      | false =>
          have hlt : g + 1 + 1 ≤ t + 1 := ble_shuts (t + 1) (g + 1) hb
          show assay s (t + 1) (lift (g + 1 + 1) (perch (t + 1) gs))
            = assay s (t + 1) ((g + 1) :: gs) + 1
          rw [the_lift_reads_above s (perch (t + 1) gs) (t + 1) (g + 1 + 1)]
          have hidx : t + 1 + (g + 1 + 1) = t + g + 2 + 1 :=
            congrArg (· + 1) (congrArg (· + 1) (seat_shuffles t g))
          rw [hidx]
          rw [the_perch_pays (t + 1) s hg gs (t + g + 2) hs]
          show s (t + g + 2 + 1) + assay s (t + g + 2 + 1) gs
            = (s (t + 1 + g + 1) + assay s (t + 1 + g + 1 + 1) gs) + 1
          rw [seat_shuffles t g]
          have hgn : s (t + g + 2 + 1) = s (t + g + 2) + s (g + 1) := gnomon_tn t s hg g
          rw [hgn]
          have hfg : s (g + 1) = 1 := hf g (Nat.le_of_succ_le (Nat.le_of_succ_le hlt))
          rw [hfg]
          exact seat_shuffles (s (t + g + 2)) (assay s (t + g + 2 + 1) gs)

theorem the_family_never_skips (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat) :
    W s (t + 1) (n + 1) = W s (t + 1) n ∨ W s (t + 1) (n + 1) = W s (t + 1) n + 1 := by
  cases hl : afoot (crank (t + 1) n) with
  | true =>
      exact Or.inl (the_family_holds_the_shadow t s hg hf (crank (t + 1) n)
        (the_dial_keeps_the_spread (t + 1) n) hl)
  | false =>
      exact Or.inr (the_family_moves_the_shadow t s hg hf (crank (t + 1) n)
        (the_dial_keeps_the_spread (t + 1) n) hl)

theorem the_family_never_steps_back (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat) : W s (t + 1) n ≤ W s (t + 1) (n + 1) := by
  cases the_family_never_skips t s hg hf n with
  | inl h => rw [h]; exact Nat.le_refl (W s (t + 1) n)
  | inr h => rw [h]; exact Nat.le_succ (W s (t + 1) n)

/-- info: 'Foam.Bridges.the_family_holds_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_holds_the_shadow

/-- info: 'Foam.Bridges.the_family_moves_the_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_moves_the_shadow

/-- info: 'Foam.Bridges.the_family_never_skips' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_never_skips

/-- info: 'Foam.Bridges.the_family_never_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_never_steps_back

theorem the_family_shadow_walks_the_slip (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (n : Nat),
      crank (t + 1) (W s (t + 1) n) = slip (t + 1) (crank (t + 1) n)
  | 0 => rfl
  | n + 1 => by
      cases hl : afoot (crank (t + 1) n) with
      | true =>
          show crank (t + 1) (assay s (t + 1) (tick (t + 1) (crank (t + 1) n)))
            = slip (t + 1) (tick (t + 1) (crank (t + 1) n))
          rw [the_family_holds_the_shadow t s hg hf (crank (t + 1) n)
                (the_dial_keeps_the_spread (t + 1) n) hl,
            slip_tick_lit t (crank (t + 1) n) hl]
          exact the_family_shadow_walks_the_slip t s hg hf n
      | false =>
          show crank (t + 1) (assay s (t + 1) (tick (t + 1) (crank (t + 1) n)))
            = slip (t + 1) (tick (t + 1) (crank (t + 1) n))
          rw [the_family_moves_the_shadow t s hg hf (crank (t + 1) n)
                (the_dial_keeps_the_spread (t + 1) n) hl,
            slip_tick_unlit t (crank (t + 1) n) hl]
          exact congrArg (tick (t + 1)) (the_family_shadow_walks_the_slip t s hg hf n)

/-- info: 'Foam.Bridges.the_family_shadow_walks_the_slip' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_shadow_walks_the_slip

theorem the_slip_reads_one_down (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (gs : List Nat), Spread (t + 1) gs →
      ∀ (m : Nat), m + 1 ≤ t + 1 → assay s (m + 2) (slip (t + 1) gs) = assay s (m + 1) gs
  | [], _, _, _ => rfl
  | 0 :: gs, hs, m, hm => by
      show assay s (m + 2) (perch (t + 1) gs) = assay s (m + 1) (0 :: gs)
      have hp : assay s (m + 2) (perch (t + 1) gs) = s (m + 2) + assay s (m + 2) gs :=
        the_perch_pays (t + 1) s hg gs (m + 1) hs
      rw [hp]
      show s (m + 2) + assay s (m + 2) gs = s (m + 1) + assay s (m + 2) gs
      have hfa : s (m + 2) = 1 := hf (m + 1) hm
      have hfb : s (m + 1) = 1 := hf m (Nat.le_of_succ_le hm)
      rw [hfa, hfb]
  | (g + 1) :: gs, _, m, _ => by
      show s (m + 1 + 1 + g) + assay s (m + 1 + 1 + g + 1) gs
        = s (m + 1 + (g + 1)) + assay s (m + 1 + (g + 1) + 1) gs
      rw [seat_shuffles (m + 1) g]
      rfl

theorem the_slip_reads_the_ground (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) : ∀ (gs : List Nat), Spread (t + 1) gs →
      assay s 1 (slip (t + 1) gs) = assay s 0 gs + cond (afoot gs) 1 0
  | [], _ => rfl
  | 0 :: gs, hs => by
      show assay s 1 (perch (t + 1) gs) = (s 0 + assay s 1 gs) + 1
      have hp : assay s 1 (perch (t + 1) gs) = s 1 + assay s 1 gs :=
        the_perch_pays (t + 1) s hg gs 0 hs
      rw [hp, hz, Nat.zero_add (assay s 1 gs)]
      have hf1 : s 1 = 1 := hf 0 (Nat.zero_le (t + 1))
      rw [hf1]
      exact Nat.add_comm 1 (assay s 1 gs)
  | (g + 1) :: gs, _ => by
      show s (1 + g) + assay s (1 + g + 1) gs
        = s (0 + (g + 1)) + assay s (0 + (g + 1) + 1) gs
      rw [Nat.zero_add (g + 1), Nat.add_comm 1 g]

/-- info: 'Foam.Bridges.the_slip_reads_one_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_slip_reads_one_down

/-- info: 'Foam.Bridges.the_slip_reads_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_slip_reads_the_ground

theorem the_shadows_descend (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (j m n : Nat), m + j + 1 = t + 1 →
      coil (W s (t + 1)) (j + 1) n = assay s (m + 1) (crank (t + 1) n)
  | 0, m, n, h => by
      have hm : m + 1 = t + 1 := h
      rw [← hm]
      rfl
  | j + 1, m, n, h => by
      have h'' : m + j + 1 + 1 = t + 1 := h
      have h' : m + 1 + j + 1 = t + 1 := (congrArg (· + 1) (seat_shuffles m j)).trans h''
      have hih := the_shadows_descend t s hg hf j (m + 1) (W s (t + 1) n) h'
      show coil (W s (t + 1)) (j + 1) (W s (t + 1) n) = assay s (m + 1) (crank (t + 1) n)
      rw [hih]
      rw [the_family_shadow_walks_the_slip t s hg hf n]
      have hle : m + 1 ≤ t + 1 := by
        rw [← h']
        exact Nat.le_add_right (m + 1) (j + 1)
      exact the_slip_reads_one_down t s hg hf (crank (t + 1) n)
        (the_dial_keeps_the_spread (t + 1) n) m hle

/-- info: 'Foam.Bridges.the_shadows_descend' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadows_descend

theorem the_deepest_shadow_reads_the_ground (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    coil (W s (t + 1)) (t + 2) n
      = assay s 0 (crank (t + 1) n) + cond (afoot (crank (t + 1) n)) 1 0 := by
  have hd := the_shadows_descend t s hg hf t 0 (W s (t + 1) n)
    (congrArg (· + 1) (Nat.zero_add t))
  show coil (W s (t + 1)) (t + 1) (W s (t + 1) n)
    = assay s 0 (crank (t + 1) n) + cond (afoot (crank (t + 1) n)) 1 0
  rw [hd, the_family_shadow_walks_the_slip t s hg hf n]
  exact the_slip_reads_the_ground t s hg hf hz (crank (t + 1) n)
    (the_dial_keeps_the_spread (t + 1) n)

theorem the_cousin_carries_its_shadow (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    W s (t + 1) n + assay s 0 (crank (t + 1) n) = n := by
  have hn : assay s (t + 2) (crank (t + 1) n) = n := the_dial_reads_true (t + 1) s hg hf n
  have hsplit := the_tally_splits_at_the_ground t s hg hf hz (crank (t + 1) n)
  show assay s (t + 1) (crank (t + 1) n) + assay s 0 (crank (t + 1) n) = n
  rw [← hsplit]
  exact hn

/-- info: 'Foam.Bridges.the_deepest_shadow_reads_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_deepest_shadow_reads_the_ground

/-- info: 'Foam.Bridges.the_cousin_carries_its_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_cousin_carries_its_shadow

theorem the_family_loop_closes (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    W s (t + 1) (n + 1) + coil (W s (t + 1)) (t + 2) n = n + 1 := by
  cases hl : afoot (crank (t + 1) n) with
  | true =>
      have hstep : W s (t + 1) (n + 1) = W s (t + 1) n :=
        the_family_holds_the_shadow t s hg hf (crank (t + 1) n)
          (the_dial_keeps_the_spread (t + 1) n) hl
      have hdeep := the_deepest_shadow_reads_the_ground t s hg hf hz n
      rw [hl] at hdeep
      have hdeep' : coil (W s (t + 1)) (t + 2) n = assay s 0 (crank (t + 1) n) + 1 := hdeep
      rw [hstep, hdeep']
      rw [← Nat.add_assoc (W s (t + 1) n) (assay s 0 (crank (t + 1) n)) 1]
      rw [the_cousin_carries_its_shadow t s hg hf hz n]
  | false =>
      have hstep : W s (t + 1) (n + 1) = W s (t + 1) n + 1 :=
        the_family_moves_the_shadow t s hg hf (crank (t + 1) n)
          (the_dial_keeps_the_spread (t + 1) n) hl
      have hdeep := the_deepest_shadow_reads_the_ground t s hg hf hz n
      rw [hl] at hdeep
      have hdeep' : coil (W s (t + 1)) (t + 2) n = assay s 0 (crank (t + 1) n) := hdeep
      rw [hstep, hdeep']
      rw [seat_shuffles (W s (t + 1) n) (assay s 0 (crank (t + 1) n))]
      rw [the_cousin_carries_its_shadow t s hg hf hz n]

theorem the_grounded_family_satisfies_the_loop (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    W s (t + 1) (n + 1) = (n + 1) - coil (W s (t + 1)) (t + 2) n :=
  calc W s (t + 1) (n + 1)
      = (W s (t + 1) (n + 1) + coil (W s (t + 1)) (t + 2) n) - coil (W s (t + 1)) (t + 2) n :=
        (add_then_sub (W s (t + 1) (n + 1)) (coil (W s (t + 1)) (t + 2) n)).symm
    _ = (n + 1) - coil (W s (t + 1)) (t + 2) n := by
        rw [the_family_loop_closes t s hg hf hz n]

/-- info: 'Foam.Bridges.the_family_loop_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_loop_closes

/-- info: 'Foam.Bridges.the_grounded_family_satisfies_the_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_family_satisfies_the_loop

theorem the_tick_beats_the_gate (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (gs : List Nat), Spread (t + 1) gs →
      assay s (t + 3) (tick (t + 1) gs) = assay s (t + 3) gs + cond (roomy (t + 1) gs) 2 1
  | [], _ => by
      show s (t + 3) + 0 = 0 + 2
      have hgn : s (t + 3) = s (t + 2) + s 1 := gnomon_tn t s hg 0
      have hf2 : s (t + 2) = 1 := hf (t + 1) (Nat.le_refl (t + 1))
      have hf1 : s 1 = 1 := hf 0 (Nat.zero_le (t + 1))
      rw [hgn, hf2, hf1]
  | g :: gs, hs => by
      show assay s (t + 3) (cond (Nat.ble (t + 1) g) (perch (t + 1) (g :: gs))
          (lift (g + 1) (perch (t + 1) gs)))
        = assay s (t + 3) (g :: gs) + cond (Nat.ble (t + 1) g) 2 1
      cases hb : Nat.ble (t + 1) g with
      | true =>
          show assay s (t + 3) (perch (t + 1) (g :: gs)) = assay s (t + 3) (g :: gs) + 2
          have hp : assay s (t + 3) (perch (t + 1) (g :: gs))
              = s (t + 3) + assay s (t + 3) (g :: gs) :=
            the_perch_pays (t + 1) s hg (g :: gs) (t + 2) ⟨Nat.le_of_ble_eq_true hb, hs⟩
          rw [hp]
          have hgn : s (t + 3) = s (t + 2) + s 1 := gnomon_tn t s hg 0
          have hf2 : s (t + 2) = 1 := hf (t + 1) (Nat.le_refl (t + 1))
          have hf1 : s 1 = 1 := hf 0 (Nat.zero_le (t + 1))
          rw [hgn, hf2, hf1]
          exact Nat.add_comm 2 (assay s (t + 3) (g :: gs))
      | false =>
          have hlt : g + 1 ≤ t + 1 := ble_shuts (t + 1) g hb
          show assay s (t + 3) (lift (g + 1) (perch (t + 1) gs)) = assay s (t + 3) (g :: gs) + 1
          rw [the_lift_reads_above s (perch (t + 1) gs) (t + 3) (g + 1)]
          have h3 : t + 1 + g = t + g + 1 := seat_shuffles t g
          have h2 : t + 2 + g = t + g + 2 :=
            (seat_shuffles (t + 1) g).trans (congrArg (· + 1) h3)
          have h1 : t + 3 + g = t + g + 3 :=
            (seat_shuffles (t + 2) g).trans (congrArg (· + 1) h2)
          have hidx : t + 3 + (g + 1) = t + g + 3 + 1 := congrArg (· + 1) h1
          rw [hidx]
          rw [the_perch_pays (t + 1) s hg gs (t + g + 3) hs]
          show s (t + g + 3 + 1) + assay s (t + g + 3 + 1) gs
            = (s (t + 3 + g) + assay s (t + 3 + g + 1) gs) + 1
          rw [h1]
          have hgn : s (t + g + 3 + 1) = s (t + g + 3) + s (g + 2) := gnomon_tn t s hg (g + 1)
          rw [hgn]
          have hfg : s (g + 2) = 1 := hf (g + 1) hlt
          rw [hfg]
          exact seat_shuffles (s (t + g + 3)) (assay s (t + g + 3 + 1) gs)

theorem the_family_beat_reads_the_gate (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) :
    stime s (t + 1) (v + 1) = stime s (t + 1) v + cond (roomy (t + 1) (crank (t + 1) v)) 2 1 :=
  the_tick_beats_the_gate t s hg hf (crank (t + 1) v) (the_dial_keeps_the_spread (t + 1) v)

theorem the_family_clock_never_stalls (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) : stime s (t + 1) v < stime s (t + 1) (v + 1) := by
  rw [the_family_beat_reads_the_gate t s hg hf v]
  cases roomy (t + 1) (crank (t + 1) v) with
  | true => exact Nat.le_succ (stime s (t + 1) v + 1)
  | false => exact Nat.le_refl (stime s (t + 1) v + 1)

theorem the_family_clock_never_leaps (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) : stime s (t + 1) (v + 1) ≤ stime s (t + 1) v + 2 := by
  rw [the_family_beat_reads_the_gate t s hg hf v]
  cases roomy (t + 1) (crank (t + 1) v) with
  | true => exact Nat.le_refl (stime s (t + 1) v + 2)
  | false => exact Nat.add_le_add_left (Nat.le_succ 1) (stime s (t + 1) v)

/-- info: 'Foam.Bridges.the_tick_beats_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_beats_the_gate

/-- info: 'Foam.Bridges.the_family_beat_reads_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_beat_reads_the_gate

/-- info: 'Foam.Bridges.the_family_clock_never_stalls' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_clock_never_stalls

/-- info: 'Foam.Bridges.the_family_clock_never_leaps' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_clock_never_leaps

theorem tick_rides_the_lift (t : Nat) : ∀ (gs : List Nat), roomy (t + 1) gs = false →
    tick (t + 1) (lift 1 gs) = lift 1 (tick (t + 1) gs)
  | [], h => nomatch h
  | g :: gs, h => by
      have hlt : g + 1 ≤ t + 1 := ble_shuts (t + 1) g h
      cases at_the_rail (g + 1) (t + 1) hlt with
      | inr heq =>
          have hgt : g = t := Nat.succ.inj heq
          subst hgt
          show cond (Nat.ble (g + 1) (g + 1)) (perch (g + 1) ((g + 1) :: gs))
              (lift (g + 1 + 1) (perch (g + 1) gs))
            = lift 1 (cond (Nat.ble (g + 1) g) (perch (g + 1) (g :: gs))
                (lift (g + 1) (perch (g + 1) gs)))
          rw [ble_mirrors (g + 1), ble_steps_back g]
          show cond (Nat.beq (g + 1) (g + 1)) (lift (g + 1 + 1) (perch (g + 1) gs))
              (0 :: (g + 1 - 1) :: gs)
            = lift 1 (lift (g + 1) (perch (g + 1) gs))
          rw [beq_mirrors (g + 1), the_lift_stacks (g + 1) (perch (g + 1) gs)]
          rfl
      | inl hlt2 =>
          have hble1 : Nat.ble (t + 1) (g + 1) = false := ble_shuts_high (g + 1) (t + 1) hlt2
          have hb : Nat.ble (t + 1) g = false := h
          show cond (Nat.ble (t + 1) (g + 1)) (perch (t + 1) ((g + 1) :: gs))
              (lift (g + 1 + 1) (perch (t + 1) gs))
            = lift 1 (cond (Nat.ble (t + 1) g) (perch (t + 1) (g :: gs))
                (lift (g + 1) (perch (t + 1) gs)))
          rw [hble1, hb]
          show lift (g + 1 + 1) (perch (t + 1) gs) = lift 1 (lift (g + 1) (perch (t + 1) gs))
          rw [the_lift_stacks (g + 1) (perch (t + 1) gs)]

theorem tick_twice_rides_the_lift (t : Nat) : ∀ (gs : List Nat), roomy (t + 1) gs = true →
    tick (t + 1) (tick (t + 1) (lift 1 gs)) = lift 1 (tick (t + 1) gs)
  | [], _ => rfl
  | g :: gs, h => by
      have hle : t + 1 ≤ g := Nat.le_of_ble_eq_true h
      have hble1 : Nat.ble (t + 1) (g + 1) = true :=
        Nat.ble_eq_true_of_le (Nat.le_succ_of_le hle)
      have hbeq : Nat.beq (g + 1) (t + 1) = false := by
        cases hb2 : Nat.beq (g + 1) (t + 1) with
        | false => rfl
        | true =>
            have hgt : g = t := Nat.succ.inj (Nat.eq_of_beq_eq_true hb2)
            subst hgt
            exact absurd hle (Nat.not_succ_le_self g)
      have hb : Nat.ble (t + 1) g = true := h
      show tick (t + 1) (cond (Nat.ble (t + 1) (g + 1)) (perch (t + 1) ((g + 1) :: gs))
          (lift (g + 1 + 1) (perch (t + 1) gs)))
        = lift 1 (cond (Nat.ble (t + 1) g) (perch (t + 1) (g :: gs))
            (lift (g + 1) (perch (t + 1) gs)))
      rw [hble1, hb]
      show tick (t + 1) (cond (Nat.beq (g + 1) (t + 1)) (lift (t + 1 + 1) (perch (t + 1) gs))
          (0 :: (g + 1 - 1) :: gs))
        = lift 1 (perch (t + 1) (g :: gs))
      rw [hbeq]
      rfl

/-- info: 'Foam.Bridges.tick_rides_the_lift' does not depend on any axioms -/
#guard_msgs in #print axioms tick_rides_the_lift

/-- info: 'Foam.Bridges.tick_twice_rides_the_lift' does not depend on any axioms -/
#guard_msgs in #print axioms tick_twice_rides_the_lift

theorem the_family_hour_writes_the_page_above (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) :
    ∀ (v : Nat), crank (t + 1) (stime s (t + 1) v) = lift 1 (crank (t + 1) v)
  | 0 => rfl
  | v + 1 => by
      have hb := the_family_beat_reads_the_gate t s hg hf v
      cases hr : roomy (t + 1) (crank (t + 1) v) with
      | true =>
          rw [hr] at hb
          have hb' : stime s (t + 1) (v + 1) = stime s (t + 1) v + 2 := hb
          rw [hb']
          show tick (t + 1) (tick (t + 1) (crank (t + 1) (stime s (t + 1) v)))
            = lift 1 (tick (t + 1) (crank (t + 1) v))
          rw [the_family_hour_writes_the_page_above t s hg hf v]
          exact tick_twice_rides_the_lift t (crank (t + 1) v) hr
      | false =>
          rw [hr] at hb
          have hb' : stime s (t + 1) (v + 1) = stime s (t + 1) v + 1 := hb
          rw [hb']
          show tick (t + 1) (crank (t + 1) (stime s (t + 1) v))
            = lift 1 (tick (t + 1) (crank (t + 1) v))
          rw [the_family_hour_writes_the_page_above t s hg hf v]
          exact tick_rides_the_lift t (crank (t + 1) v) hr

/-- info: 'Foam.Bridges.the_family_hour_writes_the_page_above' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_hour_writes_the_page_above

theorem the_family_arrives_on_the_hour (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) : W s (t + 1) (stime s (t + 1) v) = v := by
  show assay s (t + 1) (crank (t + 1) (stime s (t + 1) v)) = v
  rw [the_family_hour_writes_the_page_above t s hg hf v]
  rw [the_lift_reads_above s (crank (t + 1) v) (t + 1) 1]
  exact the_dial_reads_true (t + 1) s hg hf v

theorem the_family_walks_at_the_first_beat (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) : W s (t + 1) (stime s (t + 1) v + 1) = v + 1 := by
  show assay s (t + 1) (tick (t + 1) (crank (t + 1) (stime s (t + 1) v))) = v + 1
  rw [the_family_hour_writes_the_page_above t s hg hf v]
  rw [the_family_moves_the_shadow t s hg hf (lift 1 (crank (t + 1) v))
      (the_lift_keeps_the_spread (t + 1) 1 (crank (t + 1) v)
        (the_dial_keeps_the_spread (t + 1) v))
      (the_lift_rests_the_gate 0 (crank (t + 1) v))]
  rw [the_lift_reads_above s (crank (t + 1) v) (t + 1) 1]
  rw [the_dial_reads_true (t + 1) s hg hf v]

theorem the_family_reads_its_hours (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (v j : Nat),
      stime s (t + 1) v + j + 1 ≤ stime s (t + 1) (v + 1) →
        W s (t + 1) (stime s (t + 1) v + j + 1) = v + 1
  | v, 0, _ => the_family_walks_at_the_first_beat t s hg hf v
  | v, 1, h => by
      have heq : stime s (t + 1) (v + 1) = stime s (t + 1) v + 2 :=
        Nat.le_antisymm (the_family_clock_never_leaps t s hg hf v) h
      rw [show stime s (t + 1) v + 1 + 1 = stime s (t + 1) (v + 1) from heq.symm]
      exact the_family_arrives_on_the_hour t s hg hf (v + 1)
  | v, j + 2, h => by
      have hle : stime s (t + 1) v + (j + 3) ≤ stime s (t + 1) v + 2 :=
        Nat.le_trans h (the_family_clock_never_leaps t s hg hf v)
      exact absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
        (stack_free (stime s (t + 1) v) (j + 3) 2 hle))) (Nat.not_succ_le_zero j)

theorem the_family_is_clocked (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : Clocked (W s (t + 1)) :=
  ⟨stime s (t + 1), rfl, the_family_clock_never_stalls t s hg hf,
    the_family_reads_its_hours t s hg hf⟩

/-- info: 'Foam.Bridges.the_family_arrives_on_the_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_arrives_on_the_hour

/-- info: 'Foam.Bridges.the_family_walks_at_the_first_beat' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_walks_at_the_first_beat

/-- info: 'Foam.Bridges.the_family_reads_its_hours' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reads_its_hours

/-- info: 'Foam.Bridges.the_family_is_clocked' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_is_clocked

theorem the_family_clock_adds_the_deep_shadow (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (v : Nat) :
    stime s (t + 1) v = v + coil (W s (t + 1)) (t + 1) v := by
  have hsplit := tally_gnomon (t + 1) s hg (crank (t + 1) v) 0
  rw [Nat.zero_add (t + 1)] at hsplit
  have hs' : stime s (t + 1) v
      = assay s (t + 1 + 1) (crank (t + 1) v) + assay s (0 + 1) (crank (t + 1) v) := hsplit
  rw [hs']
  rw [the_dial_reads_true (t + 1) s hg hf v]
  have hd := the_shadows_descend t s hg hf t 0 v (congrArg (· + 1) (Nat.zero_add t))
  rw [← hd]

/-- info: 'Foam.Bridges.the_family_clock_adds_the_deep_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_clock_adds_the_deep_shadow

theorem the_family_is_registered (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : Registered (W s (t + 1)) s t :=
  ⟨fun n => spell (crank (t + 1) n),
    fun n => (the_spelling_prices_true s (crank (t + 1) n) (t + 2)).trans
      (the_dial_reads_true (t + 1) s hg hf n),
    fun n => (the_spelling_prices_true s (crank (t + 1) n) (t + 1)).symm⟩

theorem the_family_reads_a_page (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : Paged (W s (t + 1)) :=
  ⟨t + 1, t, s, hg, hf, the_family_is_registered t s hg hf⟩

theorem the_family_reads_in_both_modes (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : Paged (W s (t + 1)) ∧ Clocked (W s (t + 1)) :=
  ⟨the_family_reads_a_page t s hg hf, the_family_is_clocked t s hg hf⟩

/-- info: 'Foam.Bridges.the_family_is_registered' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_is_registered

/-- info: 'Foam.Bridges.the_family_reads_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reads_a_page

/-- info: 'Foam.Bridges.the_family_reads_in_both_modes' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reads_in_both_modes

theorem the_whole_family_walks (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) :
    (∀ n, W s (t + 1) (n + 1) + coil (W s (t + 1)) (t + 2) n = n + 1)
      ∧ Paged (W s (t + 1)) ∧ Clocked (W s (t + 1)) :=
  ⟨the_family_loop_closes t s hg hf hz, the_family_reads_a_page t s hg hf,
    the_family_is_clocked t s hg hf⟩

/-- info: 'Foam.Bridges.the_whole_family_walks' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_family_walks

theorem the_stairway_climbs_the_golden_staircase (n : Nat) : stair 1 (n + 1) = fibN (n + 1) :=
  the_golden_grammar_names_fibonacci (stair 1) (the_stairway_holds_the_gnomon 1)
    (the_stairway_holds_the_floor 1) n

/-- info: 'Foam.Bridges.the_stairway_climbs_the_golden_staircase' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_climbs_the_golden_staircase

theorem stretch_never_blanks : ∀ (g : Nat) (bs : List Bool), bs ≠ [] → stretch g bs ≠ []
  | 0, _, h => h
  | _ + 1, _, _ => fun h => nomatch h

theorem capped_stretch : ∀ (g : Nat) (bs : List Bool),
    capped bs = true → bs ≠ [] → capped (stretch g bs) = true
  | 0, _, h, _ => h
  | g + 1, bs, h, hne => by
      show capped (false :: stretch g bs) = true
      cases hx : stretch g bs with
      | nil => exact absurd hx (stretch_never_blanks g bs hne)
      | cons b bs' =>
          rw [capped_step false b bs', ← hx]
          exact capped_stretch g bs h hne

theorem the_spelling_wears_the_cap : ∀ (gs : List Nat), capped (spell gs) = true
  | [] => rfl
  | g :: gs => by
      show capped (stretch g (true :: spell gs)) = true
      apply capped_stretch g (true :: spell gs)
      · rw [capped_true_cons (spell gs)]
        exact the_spelling_wears_the_cap gs
      · exact fun h => nomatch h

/-- info: 'Foam.Bridges.stretch_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms stretch_never_blanks

/-- info: 'Foam.Bridges.capped_stretch' does not depend on any axioms -/
#guard_msgs in #print axioms capped_stretch

/-- info: 'Foam.Bridges.the_spelling_wears_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms the_spelling_wears_the_cap

theorem the_walker_is_the_golden_cousin (n : Nat) : W fibN 1 n = G n := by
  have hw : worth 2 (spell (crank 1 n)) = worth 2 (odometer n) :=
    ((worth_is_the_golden_price (spell (crank 1 n)) 2).trans
      ((the_spelling_prices_true fibN (crank 1 n) 2).trans
        (the_dial_reads_true 1 fibN the_golden_staircase_holds_the_gnomon
          the_golden_staircase_holds_the_floor n))).trans
      (the_odometer_reads_true n).symm
  have hpage : spell (crank 1 n) = odometer n :=
    two_spaced_pages_of_one_worth_are_one_page (spell (crank 1 n)) (odometer n)
      (a_gapped_page_is_spaced (spell (crank 1 n))
        (the_spelling_keeps_the_gaps 1 (crank 1 n) (the_dial_keeps_the_spread 1 n)))
      (the_odometer_spaces n)
      (the_spelling_wears_the_cap (crank 1 n))
      (the_odometer_wastes_no_seats n)
      hw
  show assay fibN 1 (crank 1 n) = worth 1 (odometer n)
  rw [← hpage, worth_is_the_golden_price (spell (crank 1 n)) 1,
    the_spelling_prices_true fibN (crank 1 n) 1]

theorem the_drover_is_the_herd_cousin (n : Nat) : W herdN 2 n = H n := by
  have hw : graze 3 (spell (crank 2 n)) = graze 3 (hodometer n) :=
    ((graze_is_the_herds_price (spell (crank 2 n)) 3).trans
      ((the_spelling_prices_true herdN (crank 2 n) 3).trans
        (the_dial_reads_true 2 herdN the_herd_holds_the_gnomon
          the_herd_holds_the_floor n))).trans
      (the_hodometer_reads_true n).symm
  have hpage : spell (crank 2 n) = hodometer n :=
    two_sparse_pages_of_one_graze_are_one_page (spell (crank 2 n)) (hodometer n)
      (a_gapped_page_is_sparse (spell (crank 2 n))
        (the_spelling_keeps_the_gaps 2 (crank 2 n) (the_dial_keeps_the_spread 2 n)))
      (the_hodometer_spaces n)
      (the_spelling_wears_the_cap (crank 2 n))
      (the_hodometer_wastes_no_seats n)
      hw
  show assay herdN 2 (crank 2 n) = graze 2 (hodometer n)
  rw [← hpage, graze_is_the_herds_price (spell (crank 2 n)) 2,
    the_spelling_prices_true herdN (crank 2 n) 2]

/-- info: 'Foam.Bridges.the_walker_is_the_golden_cousin' does not depend on any axioms -/
#guard_msgs in #print axioms the_walker_is_the_golden_cousin

/-- info: 'Foam.Bridges.the_drover_is_the_herd_cousin' does not depend on any axioms -/
#guard_msgs in #print axioms the_drover_is_the_herd_cousin

theorem the_family_reseals_the_golden_loop (n : Nat) : G (n + 1) + G (G n) = n + 1 := by
  have h := the_family_loop_closes 0 fibN the_golden_staircase_holds_the_gnomon
    the_golden_staircase_holds_the_floor rfl n
  have h' : W fibN 1 (n + 1) + W fibN 1 (W fibN 1 n) = n + 1 := h
  rw [the_walker_is_the_golden_cousin (n + 1), the_walker_is_the_golden_cousin n] at h'
  rw [the_walker_is_the_golden_cousin (G n)] at h'
  exact h'

/-- info: 'Foam.Bridges.the_family_reseals_the_golden_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_golden_loop

theorem the_next_cousin_hums :
    (W (stair 3) 3 0, W (stair 3) 3 1, W (stair 3) 3 2, W (stair 3) 3 3, W (stair 3) 3 4,
      W (stair 3) 3 5, W (stair 3) 3 6, W (stair 3) 3 7, W (stair 3) 3 8, W (stair 3) 3 9,
      W (stair 3) 3 10, W (stair 3) 3 11)
      = (0, 1, 1, 2, 3, 4, 5, 5, 6, 6, 7, 8) := rfl

theorem the_next_clock_hums :
    (stime (stair 3) 3 0, stime (stair 3) 3 1, stime (stair 3) 3 2, stime (stair 3) 3 3,
      stime (stair 3) 3 4, stime (stair 3) 3 5, stime (stair 3) 3 6, stime (stair 3) 3 7)
      = (0, 2, 3, 4, 5, 7, 9, 10) := rfl

theorem the_next_cousin_closes_its_loop (n : Nat) :
    W (stair 3) 3 (n + 1) + coil (W (stair 3) 3) 4 n = n + 1 :=
  the_family_loop_closes 2 (stair 3) (the_stairway_holds_the_gnomon 3)
    (the_stairway_holds_the_floor 3) rfl n

theorem the_next_cousin_reads_in_both_modes : Paged (W (stair 3) 3) ∧ Clocked (W (stair 3) 3) :=
  the_family_reads_in_both_modes 2 (stair 3) (the_stairway_holds_the_gnomon 3)
    (the_stairway_holds_the_floor 3)

/-- info: 'Foam.Bridges.the_next_cousin_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_cousin_hums

/-- info: 'Foam.Bridges.the_next_clock_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_clock_hums

/-- info: 'Foam.Bridges.the_next_cousin_closes_its_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_cousin_closes_its_loop

/-- info: 'Foam.Bridges.the_next_cousin_reads_in_both_modes' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_cousin_reads_in_both_modes

theorem the_ground_walk_reads_the_half :
    (W peg 0 0, W peg 0 1, W peg 0 2, W peg 0 3, W peg 0 4, W peg 0 5, W peg 0 6, W peg 0 7)
      = (0, 0, 1, 1, 2, 2, 3, 3) := rfl

theorem the_ground_floor_breaks_the_loop :
    ¬ (W peg 0 1 + coil (W peg 0) 1 0 = 1) := fun h => nomatch h

/-- info: 'Foam.Bridges.the_ground_walk_reads_the_half' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_walk_reads_the_half

/-- info: 'Foam.Bridges.the_ground_floor_breaks_the_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_floor_breaks_the_loop

theorem the_wild_walk_is_no_cousin (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ¬ (∀ n, Q n = W s (t + 1) n) := fun hq => by
  have h : (49 : Nat) ≤ W s (t + 1) 49 + W s (t + 1) 49 :=
    a_paged_walk_holds_the_half (W s (t + 1)) (the_family_reads_a_page t s hg hf) 49
  rw [← hq 49, the_wild_walk_undercuts_the_half] at h
  exact absurd h (Nat.not_succ_le_self 48)

/-- info: 'Foam.Bridges.the_wild_walk_is_no_cousin' does not depend on any axioms -/
#guard_msgs in #print axioms the_wild_walk_is_no_cousin

theorem one_grammar_one_cousin (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat) : W s (t + 1) n = W (stair (t + 1)) (t + 1) n :=
  one_grammar_one_tally s (stair (t + 1))
    (fun k => the_grammar_names_its_staircase (t + 1) s (stair (t + 1)) hg hf
      (the_stairway_holds_the_gnomon (t + 1)) (the_stairway_holds_the_floor (t + 1)) k)
    (crank (t + 1) n) t

/-- info: 'Foam.Bridges.one_grammar_one_cousin' does not depend on any axioms -/
#guard_msgs in #print axioms one_grammar_one_cousin

theorem the_spelling_comes_home : ∀ (ds : List Bool), capped ds = true →
    spell (unspell ds) = ds
  | [], _ => rfl
  | true :: ds, hc => by
      have hc' : capped ds = true := by
        rw [capped_true_cons ds] at hc
        exact hc
      show true :: spell (unspell ds) = true :: ds
      rw [the_spelling_comes_home ds hc']
  | false :: ds, hc => by
      have ih := the_spelling_comes_home ds (capped_tail hc)
      cases hds : unspell ds with
      | nil =>
          rw [hds] at ih
          exact absurd ih.symm (capped_tail_ne_nil hc)
      | cons g gs =>
          rw [hds] at ih
          rw [unspell_step ds g gs hds]
          show false :: spell (g :: gs) = false :: ds
          rw [ih]

/-- info: 'Foam.Bridges.the_spelling_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_spelling_comes_home

theorem two_gapped_pages_of_one_price_are_one_page (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (ds es : List Bool)
    (hgd : Gapped e ds) (hge : Gapped e es)
    (hcd : capped ds = true) (hce : capped es = true)
    (hw : price s (e + 1) ds = price s (e + 1) es) : ds = es := by
  have hd : assay s (e + 1) (unspell ds) = price s (e + 1) ds := by
    rw [← the_spelling_prices_true s (unspell ds) (e + 1), the_spelling_comes_home ds hcd]
  have he : assay s (e + 1) (unspell es) = price s (e + 1) es := by
    rw [← the_spelling_prices_true s (unspell es) (e + 1), the_spelling_comes_home es hce]
  have hpage : unspell ds = unspell es :=
    two_spread_pages_of_one_assay_are_one_page e s hg hf (unspell ds) (unspell es)
      (the_unspelling_spreads e ds hgd) (the_unspelling_spreads e es hge)
      (hd.trans (hw.trans he.symm))
  rw [← the_spelling_comes_home ds hcd, ← the_spelling_comes_home es hce, hpage]

/-- info: 'Foam.Bridges.two_gapped_pages_of_one_price_are_one_page' does not depend on any axioms -/
#guard_msgs in #print axioms two_gapped_pages_of_one_price_are_one_page

theorem the_family_reseals_the_golden_uniqueness (ds es : List Bool)
    (hnds : NoConsec ds) (hnes : NoConsec es)
    (hcds : capped ds = true) (hces : capped es = true)
    (hw : worth 2 ds = worth 2 es) : ds = es :=
  two_gapped_pages_of_one_price_are_one_page 1 fibN the_golden_staircase_holds_the_gnomon
    the_golden_staircase_holds_the_floor ds es
    (a_spaced_page_is_gapped ds hnds) (a_spaced_page_is_gapped es hnes) hcds hces
    ((worth_is_the_golden_price ds 2).symm.trans (hw.trans (worth_is_the_golden_price es 2)))

theorem the_family_reseals_the_herd_uniqueness (ds es : List Bool)
    (hsds : Sparse ds) (hses : Sparse es)
    (hcds : capped ds = true) (hces : capped es = true)
    (hw : graze 3 ds = graze 3 es) : ds = es :=
  two_gapped_pages_of_one_price_are_one_page 2 herdN the_herd_holds_the_gnomon
    the_herd_holds_the_floor ds es
    (a_sparse_page_is_gapped ds hsds) (a_sparse_page_is_gapped es hses) hcds hces
    ((graze_is_the_herds_price ds 3).symm.trans (hw.trans (graze_is_the_herds_price es 3)))

theorem two_capped_pages_of_one_gauge_are_one_page (ds es : List Bool)
    (hcds : capped ds = true) (hces : capped es = true)
    (hw : gauge 0 ds = gauge 0 es) : ds = es :=
  two_gapped_pages_of_one_price_are_one_page 0 peg the_ruler_holds_the_gnomon
    the_ruler_holds_the_floor ds es
    (every_page_is_gapped_at_the_ground ds) (every_page_is_gapped_at_the_ground es) hcds hces
    ((gauge_is_the_rulers_price ds 0).symm.trans (hw.trans (gauge_is_the_rulers_price es 0)))

/-- info: 'Foam.Bridges.the_family_reseals_the_golden_uniqueness' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_golden_uniqueness

/-- info: 'Foam.Bridges.the_family_reseals_the_herd_uniqueness' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_herd_uniqueness

/-- info: 'Foam.Bridges.two_capped_pages_of_one_gauge_are_one_page' does not depend on any axioms -/
#guard_msgs in #print axioms two_capped_pages_of_one_gauge_are_one_page

theorem bclick_never_blanks : ∀ (ds : List Bool), bclick ds ≠ []
  | [] => fun h => nomatch h
  | false :: _ => fun h => nomatch h
  | true :: _ => fun h => nomatch h

theorem bclick_keeps_the_cap : ∀ (ds : List Bool), capped ds = true →
    capped (bclick ds) = true
  | [], _ => rfl
  | false :: ds, hc => by
      show capped (true :: ds) = true
      rw [capped_true_cons ds]
      exact capped_tail hc
  | true :: ds, hc => by
      have hcd : capped ds = true := by
        rw [capped_true_cons ds] at hc
        exact hc
      have ih := bclick_keeps_the_cap ds hcd
      show capped (false :: bclick ds) = true
      cases hb : bclick ds with
      | nil => exact absurd hb (bclick_never_blanks ds)
      | cons b bs =>
          rw [capped_step false b bs, ← hb]
          exact ih

theorem the_bodometer_wastes_no_seats : ∀ (n : Nat), capped (bodometer n) = true
  | 0 => rfl
  | n + 1 => bclick_keeps_the_cap (bodometer n) (the_bodometer_wastes_no_seats n)

/-- info: 'Foam.Bridges.bclick_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms bclick_never_blanks

/-- info: 'Foam.Bridges.bclick_keeps_the_cap' does not depend on any axioms -/
#guard_msgs in #print axioms bclick_keeps_the_cap

/-- info: 'Foam.Bridges.the_bodometer_wastes_no_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_bodometer_wastes_no_seats

theorem the_golden_crank_writes_the_golden_page (n : Nat) :
    spell (crank 1 n) = odometer n :=
  two_gapped_pages_of_one_price_are_one_page 1 fibN the_golden_staircase_holds_the_gnomon
    the_golden_staircase_holds_the_floor (spell (crank 1 n)) (odometer n)
    (the_spelling_keeps_the_gaps 1 (crank 1 n) (the_dial_keeps_the_spread 1 n))
    (a_spaced_page_is_gapped (odometer n) (the_odometer_spaces n))
    (the_spelling_wears_the_cap (crank 1 n))
    (the_odometer_wastes_no_seats n)
    ((the_spelling_prices_true fibN (crank 1 n) 2).trans
      ((the_dial_reads_true 1 fibN the_golden_staircase_holds_the_gnomon
          the_golden_staircase_holds_the_floor n).trans
        ((the_odometer_reads_true n).symm.trans
          (worth_is_the_golden_price (odometer n) 2))))

theorem the_herd_crank_writes_the_herd_page (n : Nat) :
    spell (crank 2 n) = hodometer n :=
  two_gapped_pages_of_one_price_are_one_page 2 herdN the_herd_holds_the_gnomon
    the_herd_holds_the_floor (spell (crank 2 n)) (hodometer n)
    (the_spelling_keeps_the_gaps 2 (crank 2 n) (the_dial_keeps_the_spread 2 n))
    (a_sparse_page_is_gapped (hodometer n) (the_hodometer_spaces n))
    (the_spelling_wears_the_cap (crank 2 n))
    (the_hodometer_wastes_no_seats n)
    ((the_spelling_prices_true herdN (crank 2 n) 3).trans
      ((the_dial_reads_true 2 herdN the_herd_holds_the_gnomon
          the_herd_holds_the_floor n).trans
        ((the_hodometer_reads_true n).symm.trans
          (graze_is_the_herds_price (hodometer n) 3))))

theorem the_ground_crank_writes_the_binary_page (n : Nat) :
    spell (crank 0 n) = bodometer n :=
  two_gapped_pages_of_one_price_are_one_page 0 peg the_ruler_holds_the_gnomon
    the_ruler_holds_the_floor (spell (crank 0 n)) (bodometer n)
    (every_page_is_gapped_at_the_ground (spell (crank 0 n)))
    (every_page_is_gapped_at_the_ground (bodometer n))
    (the_spelling_wears_the_cap (crank 0 n))
    (the_bodometer_wastes_no_seats n)
    ((the_spelling_prices_true peg (crank 0 n) 1).trans
      ((the_dial_reads_true 0 peg the_ruler_holds_the_gnomon
          the_ruler_holds_the_floor n).trans
        ((the_bodometer_reads_true n).symm.trans
          (gauge_is_the_rulers_price (bodometer n) 0))))

theorem three_machines_one_crank (n : Nat) :
    spell (crank 0 n) = bodometer n
      ∧ spell (crank 1 n) = odometer n
      ∧ spell (crank 2 n) = hodometer n :=
  ⟨the_ground_crank_writes_the_binary_page n, the_golden_crank_writes_the_golden_page n,
    the_herd_crank_writes_the_herd_page n⟩

/-- info: 'Foam.Bridges.the_golden_crank_writes_the_golden_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_golden_crank_writes_the_golden_page

/-- info: 'Foam.Bridges.the_herd_crank_writes_the_herd_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_crank_writes_the_herd_page

/-- info: 'Foam.Bridges.the_ground_crank_writes_the_binary_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_crank_writes_the_binary_page

/-- info: 'Foam.Bridges.three_machines_one_crank' does not depend on any axioms -/
#guard_msgs in #print axioms three_machines_one_crank

theorem the_family_beacon_slides (t k : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : W s (t + 1) (s (t + k + 2)) = s (t + k + 1) := by
  have hb := the_crank_at_a_stair_number_is_one_stride (t + 1) k s hg hf
  rw [show t + 1 + k + 1 = t + k + 2 from congrArg (· + 1) (seat_shuffles t k)] at hb
  show assay s (t + 1) (crank (t + 1) (s (t + k + 2))) = s (t + k + 1)
  rw [hb]
  show s (t + 1 + k) + 0 = s (t + k + 1)
  rw [seat_shuffles t k]
  rfl

theorem the_family_reseals_the_golden_slide (k : Nat) : G (fibN (k + 2)) = fibN (k + 1) := by
  have h := the_family_beacon_slides 0 k fibN the_golden_staircase_holds_the_gnomon
    the_golden_staircase_holds_the_floor
  rw [Nat.zero_add k, the_walker_is_the_golden_cousin (fibN (k + 2))] at h
  exact h

/-- info: 'Foam.Bridges.the_family_beacon_slides' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_beacon_slides

/-- info: 'Foam.Bridges.the_family_reseals_the_golden_slide' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_golden_slide

def veil (e : Nat) : List Nat → Bool
  | [] => false
  | [0] => true
  | [p + 1] => Nat.beq (brand e p).2 1
  | _ :: _ :: _ => false

def sash (e : Nat) : List Nat → Bool
  | [] => false
  | [0] => false
  | [p + 1] => Nat.beq (brand e p).2 0
  | _ :: _ :: _ => false

def bride (s : Nat → Nat) (e n : Nat) : Nat :=
  W s e n + cond (veil e (crank e (n + 1))) 1 0

def groom (s : Nat → Nat) (e n : Nat) : Nat :=
  W s e n - cond (sash e (crank e (n + 1))) 1 0

theorem the_family_bride_wakes_lit (t : Nat) (s : Nat → Nat) : bride s (t + 1) 0 = 1 := rfl

theorem the_family_groom_wakes_dark (t : Nat) (s : Nat → Nat) : groom s (t + 1) 0 = 0 := rfl

theorem the_family_bride_reads_the_shared_page (s : Nat → Nat) (e n : Nat) :
    bride s e n = assay s e (crank e n)
      + cond (veil e (tick e (crank e n))) 1 0 := rfl

theorem the_family_groom_reads_the_shared_page (s : Nat → Nat) (e n : Nat) :
    groom s e n = assay s e (crank e n)
      - cond (sash e (tick e (crank e n))) 1 0 := rfl

/-- info: 'Foam.Bridges.the_family_bride_wakes_lit' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_bride_wakes_lit

/-- info: 'Foam.Bridges.the_family_groom_wakes_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_groom_wakes_dark

/-- info: 'Foam.Bridges.the_family_bride_reads_the_shared_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_bride_reads_the_shared_page

/-- info: 'Foam.Bridges.the_family_groom_reads_the_shared_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_groom_reads_the_shared_page

theorem the_veil_finds_its_beacon (e : Nat) (gs : List Nat) (h : veil e gs = true) :
    gs = [0] ∨ ∃ p, gs = [p + 1] ∧ Nat.beq (brand e p).2 1 = true := by
  match gs, h with
  | 0 :: [], _ => exact Or.inl rfl
  | (p + 1) :: [], h => exact Or.inr ⟨p, rfl, h⟩

theorem the_sash_finds_its_beacon (e : Nat) (gs : List Nat) (h : sash e gs = true) :
    ∃ p, gs = [p + 1] ∧ Nat.beq (brand e p).2 0 = true := by
  match gs, h with
  | 0 :: [], h => exact nomatch h
  | (p + 1) :: [], h => exact ⟨p, rfl, h⟩

theorem the_veil_and_sash_never_meet (e : Nat) (gs : List Nat) (h : veil e gs = true) :
    sash e gs = false := by
  match gs, h with
  | 0 :: [], _ => rfl
  | (p + 1) :: [], h =>
      have h1 : (brand e p).2 = 1 := Nat.eq_of_beq_eq_true h
      show Nat.beq (brand e p).2 0 = false
      rw [h1]
      rfl

/-- info: 'Foam.Bridges.the_veil_finds_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_veil_finds_its_beacon

/-- info: 'Foam.Bridges.the_sash_finds_its_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_sash_finds_its_beacon

/-- info: 'Foam.Bridges.the_veil_and_sash_never_meet' does not depend on any axioms -/
#guard_msgs in #print axioms the_veil_and_sash_never_meet

theorem the_veil_rests_above_a_tall_stair (e m : Nat) :
    veil e (tick e [m + 2]) = false := by
  cases Nat.decLe (m + 2) e with
  | isTrue hle =>
      rw [the_tick_climbs_the_floor e (m + 2) hle]
      show Nat.beq (brand e (m + 2)).2 1 = false
      have hbr : brand e (0 + (m + 2)) = (0, m + 2) :=
        the_brand_climbs_the_rungs e 0 (m + 2) hle
      rw [Nat.zero_add (m + 2)] at hbr
      rw [hbr]
      exact beq_shuts_high 1 (m + 2) (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m)))
  | isFalse hgt =>
      have hlt : e + 1 ≤ m + 2 := Nat.gt_of_not_le hgt
      match Nat.le.dest hlt with
      | ⟨w, hw⟩ =>
          have hw' : tick e [e + 1 + w] = [0, e + w] := the_tick_leaves_the_rail e w
          rw [hw] at hw'
          rw [hw']
          rfl

theorem the_sash_rests_above_a_tall_stair (e m : Nat) :
    sash e (tick e [m + 2]) = false := by
  cases Nat.decLe (m + 2) e with
  | isTrue hle =>
      rw [the_tick_climbs_the_floor e (m + 2) hle]
      show Nat.beq (brand e (m + 2)).2 0 = false
      have hbr : brand e (0 + (m + 2)) = (0, m + 2) :=
        the_brand_climbs_the_rungs e 0 (m + 2) hle
      rw [Nat.zero_add (m + 2)] at hbr
      rw [hbr]
      exact beq_shuts_high 0 (m + 2) (Nat.succ_le_succ (Nat.zero_le (m + 1)))
  | isFalse hgt =>
      have hlt : e + 1 ≤ m + 2 := Nat.gt_of_not_le hgt
      match Nat.le.dest hlt with
      | ⟨w, hw⟩ =>
          have hw' : tick e [e + 1 + w] = [0, e + w] := the_tick_leaves_the_rail e w
          rw [hw] at hw'
          rw [hw']
          rfl

/-- info: 'Foam.Bridges.the_veil_rests_above_a_tall_stair' does not depend on any axioms -/
#guard_msgs in #print axioms the_veil_rests_above_a_tall_stair

/-- info: 'Foam.Bridges.the_sash_rests_above_a_tall_stair' does not depend on any axioms -/
#guard_msgs in #print axioms the_sash_rests_above_a_tall_stair

theorem the_floor_reads_one (t : Nat) (s : Nat → Nat) (hf : Floored (t + 1) s) :
    s (t + 1) = 1 := hf t (Nat.le_succ t)

theorem the_rail_reads_one (t : Nat) (s : Nat → Nat) (hf : Floored (t + 1) s) :
    s (t + 2) = 1 := hf (t + 1) (Nat.le_refl (t + 1))

theorem the_first_flight_reads_two (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : s (t + 3) = 2 := by
  have h := gnomon_tn t s hg 0
  rw [the_rail_reads_one t s hf, hf 0 (Nat.zero_le (t + 1))] at h
  exact h

theorem the_second_flight_reads_three (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : s (t + 4) = 3 := by
  have h := gnomon_tn t s hg 1
  rw [the_first_flight_reads_two t s hg hf, hf 1 (Nat.succ_le_succ (Nat.zero_le t))] at h
  exact h

/-- info: 'Foam.Bridges.the_floor_reads_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_floor_reads_one

/-- info: 'Foam.Bridges.the_rail_reads_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_rail_reads_one

/-- info: 'Foam.Bridges.the_first_flight_reads_two' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_flight_reads_two

/-- info: 'Foam.Bridges.the_second_flight_reads_three' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_flight_reads_three

theorem the_walk_glows_on_a_written_page (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (g : Nat) (gs : List Nat) :
    1 ≤ assay s (t + 1) (g :: gs) := by
  show 1 ≤ s (t + 1 + g) + assay s (t + 1 + g + 1) gs
  rw [seat_shuffles t g]
  exact Nat.le_trans (a_grammar_glows (t + 1) s hg hf (t + g))
    (Nat.le_add_right (s (t + g + 1)) (assay s (t + g + 1 + 1) gs))

theorem a_crossing_reads_its_stair (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n k : Nat) (h : crank (t + 1) (n + 1) = [k]) :
    n + 1 = s (t + k + 2) := by
  have hd := the_dial_reads_true (t + 1) s hg hf (n + 1)
  rw [h] at hd
  show n + 1 = s (t + k + 1 + 1)
  rw [← seat_shuffles t k, ← seat_shuffles (t + 1) k]
  exact hd.symm

/-- info: 'Foam.Bridges.the_walk_glows_on_a_written_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_glows_on_a_written_page

/-- info: 'Foam.Bridges.a_crossing_reads_its_stair' does not depend on any axioms -/
#guard_msgs in #print axioms a_crossing_reads_its_stair

theorem the_walk_holds_the_groom (t : Nat) (s : Nat → Nat) (n : Nat) :
    groom s (t + 1) n ≤ W s (t + 1) n :=
  the_toll_never_gains (W s (t + 1) n) (cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0)

theorem the_bride_holds_the_walk (t : Nat) (s : Nat → Nat) (n : Nat) :
    W s (t + 1) n ≤ bride s (t + 1) n :=
  Nat.le_add_right (W s (t + 1) n) (cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0)

theorem the_household_holds_the_walk (t : Nat) (s : Nat → Nat) (n : Nat) :
    groom s (t + 1) n ≤ W s (t + 1) n ∧ W s (t + 1) n ≤ bride s (t + 1) n :=
  ⟨the_walk_holds_the_groom t s n, the_bride_holds_the_walk t s n⟩

/-- info: 'Foam.Bridges.the_walk_holds_the_groom' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_holds_the_groom

/-- info: 'Foam.Bridges.the_bride_holds_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_holds_the_walk

/-- info: 'Foam.Bridges.the_household_holds_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_household_holds_the_walk

theorem the_spouses_disagree_on_the_shallow_stairs (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n : Nat) :
    groom s (t + 1) n
        + cond (veil (t + 1) (crank (t + 1) (n + 1))
            || sash (t + 1) (crank (t + 1) (n + 1))) 1 0
      = bride s (t + 1) n := by
  cases hv : veil (t + 1) (crank (t + 1) (n + 1)) with
  | true =>
      have hs := the_veil_and_sash_never_meet (t + 1) (crank (t + 1) (n + 1)) hv
      show groom s (t + 1) n + 1
        = W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0
      rw [hv]
      show (W s (t + 1) n - cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0) + 1
        = W s (t + 1) n + 1
      rw [hs]
      rfl
  | false =>
      cases hs : sash (t + 1) (crank (t + 1) (n + 1)) with
      | false =>
          show groom s (t + 1) n
            = W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0
          rw [hv]
          show W s (t + 1) n - cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0
            = W s (t + 1) n + 0
          rw [hs]
          rfl
      | true =>
          match the_sash_finds_its_beacon (t + 1) (crank (t + 1) (n + 1)) hs with
          | ⟨p, hpage, _⟩ =>
            have hcn : crank (t + 1) n = untick (t + 1) (crank (t + 1) (n + 1)) :=
              the_crank_steps_back (t + 1) n
            rw [hpage] at hcn
            have hglow : 1 ≤ W s (t + 1) n := by
              show 1 ≤ assay s (t + 1) (crank (t + 1) n)
              rw [hcn]
              exact the_walk_glows_on_a_written_page t s hg hf
                (brand (t + 1) p).2 (unfurl (t + 1) (brand (t + 1) p).1 [])
            show groom s (t + 1) n + 1
              = W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0
            rw [hv]
            show (W s (t + 1) n - cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0) + 1
              = W s (t + 1) n + 0
            rw [hs]
            show (W s (t + 1) n - 1) + 1 = W s (t + 1) n + 0
            rw [sub_one_back (W s (t + 1) n) hglow]
            rfl

theorem the_household_agrees_on_the_deep_stairs (t : Nat) (s : Nat → Nat) (n : Nat)
    (hv : veil (t + 1) (crank (t + 1) (n + 1)) = false)
    (hs : sash (t + 1) (crank (t + 1) (n + 1)) = false) :
    bride s (t + 1) n = W s (t + 1) n ∧ groom s (t + 1) n = W s (t + 1) n := by
  constructor
  · show W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0 = W s (t + 1) n
    rw [hv]
    rfl
  · show W s (t + 1) n - cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0 = W s (t + 1) n
    rw [hs]
    rfl

/-- info: 'Foam.Bridges.the_spouses_disagree_on_the_shallow_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_spouses_disagree_on_the_shallow_stairs

/-- info: 'Foam.Bridges.the_household_agrees_on_the_deep_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_household_agrees_on_the_deep_stairs

theorem the_coil_rests_at_zero (t : Nat) (s : Nat → Nat) :
    ∀ (j : Nat), coil (W s (t + 1)) j 0 = 0
  | 0 => rfl
  | j + 1 => the_coil_rests_at_zero t s j

theorem the_coil_rests_at_the_floor (t : Nat) (s : Nat → Nat) (hf : Floored (t + 1) s) :
    ∀ (j : Nat), coil (W s (t + 1)) j 1 = 1
  | 0 => rfl
  | j + 1 => by
      have h1 : W s (t + 1) 1 = 1 := by
        show s (t + 1 + 0) + 0 = 1
        exact the_floor_reads_one t s hf
      show coil (W s (t + 1)) j (W s (t + 1) 1) = 1
      rw [h1]
      exact the_coil_rests_at_the_floor t s hf j

/-- info: 'Foam.Bridges.the_coil_rests_at_zero' does not depend on any axioms -/
#guard_msgs in #print axioms the_coil_rests_at_zero

/-- info: 'Foam.Bridges.the_coil_rests_at_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_coil_rests_at_the_floor

theorem coil_shuffle (t k j : Nat) : t + (k + j + 1) = t + k + j + 1 := by
  rw [← Nat.add_assoc t (k + j) 1, ← Nat.add_assoc t k j]

theorem the_beacon_rides_the_coil (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (j k : Nat),
      coil (W s (t + 1)) j (s (t + k + j + 2)) = s (t + k + 2)
  | 0, k => rfl
  | j + 1, k => by
      have hsl := the_family_beacon_slides t (k + j + 1) s hg hf
      rw [coil_shuffle t k j] at hsl
      show coil (W s (t + 1)) j (W s (t + 1) (s (t + k + j + 1 + 2))) = s (t + k + 2)
      rw [hsl]
      exact the_beacon_rides_the_coil t s hg hf j k

/-- info: 'Foam.Bridges.coil_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms coil_shuffle

/-- info: 'Foam.Bridges.the_beacon_rides_the_coil' does not depend on any axioms -/
#guard_msgs in #print axioms the_beacon_rides_the_coil

theorem the_wounded_beacon_rides_the_coil (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (p x : Nat) (hbr : (brand (t + 1) p).2 = t + 1)
    (hx : x + 1 = s (p + t + 3)) :
    coil (W s (t + 1)) t x + 1 = s (p + 3) := by
  cases t with
  | zero => exact hx
  | succ t' =>
      have hcr := the_crank_at_a_stair_number_is_one_stride (t' + 1 + 1) (p + 1) s hg hf
      have hcr' : crank (t' + 1 + 1) (s (p + (t' + 1) + 3)) = [p + 1] := by
        have hidx : t' + 1 + 1 + (p + 1) + 1 = p + (t' + 1) + 3 := by
          rw [Nat.add_comm (t' + 1 + 1) (p + 1)]
          show p + 1 + t' + 3 = p + t' + 4
          rw [seat_shuffles p t']
        rw [hidx] at hcr
        exact hcr
      rw [← hx] at hcr'
      have hcx : crank (t' + 1 + 1) x
          = (t' + 1 + 1) :: unfurl (t' + 1 + 1) (brand (t' + 1 + 1) p).1 [] := by
        rw [the_crank_steps_back (t' + 1 + 1) x, hcr']
        show (brand (t' + 1 + 1) p).2 :: unfurl (t' + 1 + 1) (brand (t' + 1 + 1) p).1 [] = _
        rw [hbr]
      have hsh := the_shadows_descend (t' + 1) s hg hf t' 1 x
        (congrArg (· + 1) (Nat.add_comm 1 t'))
      rw [hcx] at hsh
      have hpu := a_purse_and_a_stair_make_a_beacon (t' + 1 + 1) s hg
        (brand (t' + 1 + 1) p).1 (t' + 1 + 1) 1
      have hi1 : 1 + (t' + 1 + 1) + 2 = t' + 1 + 4 := by
        rw [Nat.add_comm 1 (t' + 1 + 1)]
      have hi2 : 1 + (t' + 1 + 1) + 1 = t' + 1 + 3 := by
        rw [Nat.add_comm 1 (t' + 1 + 1)]
      rw [hi1, hi2, the_second_flight_reads_three (t' + 1) s hg hf,
        the_first_flight_reads_two (t' + 1) s hg hf] at hpu
      have hrungs : rungs (t' + 1 + 1) (brand (t' + 1 + 1) p).1 + (t' + 1 + 1) = p := by
        have h := the_brand_reads_the_rungs (t' + 1 + 1) p
        rw [hbr] at h
        exact h
      have hout : 1 + rungs (t' + 1 + 1) (brand (t' + 1 + 1) p).1 + (t' + 1 + 1) + 2
          = p + 3 := by
        rw [Nat.add_comm 1 (rungs (t' + 1 + 1) (brand (t' + 1 + 1) p).1),
          Nat.add_assoc (rungs (t' + 1 + 1) (brand (t' + 1 + 1) p).1) 1 (t' + 1 + 1),
          Nat.add_comm 1 (t' + 1 + 1), ← Nat.add_assoc
            (rungs (t' + 1 + 1) (brand (t' + 1 + 1) p).1) (t' + 1 + 1) 1, hrungs]
      rw [hout] at hpu
      show coil (W s (t' + 1 + 1)) (t' + 1) x + 1 = s (p + 3)
      rw [hsh]
      exact unstack (assay s (1 + 1)
        ((t' + 1 + 1) :: unfurl (t' + 1 + 1) (brand (t' + 1 + 1) p).1 []) + 1)
        (s (p + 3)) 2 hpu

/-- info: 'Foam.Bridges.the_wounded_beacon_rides_the_coil' does not depend on any axioms -/
#guard_msgs in #print axioms the_wounded_beacon_rides_the_coil

theorem the_family_marriage_closes_for_the_bride (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    bride s (t + 1) (n + 1)
      + coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)) = n + 1 := by
  cases hv : veil (t + 1) (crank (t + 1) (n + 1)) with
  | true =>
      cases the_veil_finds_its_beacon (t + 1) (crank (t + 1) (n + 1)) hv with
      | inl h0 =>
          have hn1 : n + 1 = s (t + 0 + 2) := a_crossing_reads_its_stair t s hg hf n 0 h0
          have hn1' : n + 1 = 1 := by
            rw [hn1]
            exact the_rail_reads_one t s hf
          have hn0 : n = 0 := Nat.succ.inj hn1'
          subst hn0
          have hw1 : W s (t + 1) 1 = 1 := by
            show s (t + 1 + 0) + 0 = 1
            exact the_floor_reads_one t s hf
          have hg1 : groom s (t + 1) (bride s (t + 1) 0) = 0 := by
            show W s (t + 1) 1 - cond (sash (t + 1) (crank (t + 1) (1 + 1))) 1 0 = 0
            rw [hw1]
            rfl
          have hb1 : bride s (t + 1) (0 + 1) = 1 := by
            show W s (t + 1) 1 + cond (veil (t + 1) (crank (t + 1) (1 + 1))) 1 0 = 1
            rw [hw1]
            rfl
          rw [hb1, hg1, the_coil_rests_at_zero t s t]
      | inr hex =>
          match hex with
          | ⟨p, hpage, hres⟩ =>
            have hr1 : (brand (t + 1) p).2 = 1 := Nat.eq_of_beq_eq_true hres
            have hrp : rungs (t + 1) (brand (t + 1) p).1 + 1 = p := by
              have h := the_brand_reads_the_rungs (t + 1) p
              rw [hr1] at h
              exact h
            have hn1 : n + 1 = s (t + (p + 1) + 2) :=
              a_crossing_reads_its_stair t s hg hf n (p + 1) hpage
            have hcn : crank (t + 1) n = 1 :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
              rw [the_crank_steps_back (t + 1) n, hpage]
              show (brand (t + 1) p).2 :: unfurl (t + 1) (brand (t + 1) p).1 [] = _
              rw [hr1]
            have hpu' : assay s (t + 1) (1 :: unfurl (t + 1) (brand (t + 1) p).1 [])
                  + s (t + 3)
                = s (t + rungs (t + 1) (brand (t + 1) p).1 + 1 + 2) + s (t + 2) :=
              a_purse_and_a_stair_make_a_beacon (t + 1) s hg (brand (t + 1) p).1 1 t
            rw [the_first_flight_reads_two t s hg hf, the_rail_reads_one t s hf] at hpu'
            have hmid : t + rungs (t + 1) (brand (t + 1) p).1 + 1 + 2 = t + p + 2 := by
              rw [Nat.add_assoc t (rungs (t + 1) (brand (t + 1) p).1) 1, hrp]
            rw [hmid] at hpu'
            have hVn : W s (t + 1) n + 1 = s (t + p + 2) := by
              have hWn : W s (t + 1) n
                  = assay s (t + 1) (1 :: unfurl (t + 1) (brand (t + 1) p).1 []) := by
                show assay s (t + 1) (crank (t + 1) n) = _
                rw [hcn]
              rw [hWn]
              exact Nat.succ.inj hpu'
            have hbn : bride s (t + 1) n = s (t + p + 2) := by
              show W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0
                = s (t + p + 2)
              rw [hv]
              exact hVn
            have hcb : crank (t + 1) (s (t + p + 2)) = [p] := by
              have h := the_crank_at_a_stair_number_is_one_stride (t + 1) p s hg hf
              rw [seat_shuffles t p] at h
              exact h
            have hsashb : sash (t + 1) (crank (t + 1) (s (t + p + 2) + 1)) = false := by
              have hct : crank (t + 1) (s (t + p + 2) + 1) = tick (t + 1) [p] := by
                show tick (t + 1) (crank (t + 1) (s (t + p + 2))) = tick (t + 1) [p]
                rw [hcb]
              rw [hct]
              cases hq : (brand (t + 1) p).1 with
              | zero =>
                  have hp1 : p = 1 := by
                    rw [hq] at hrp
                    exact hrp.symm
                  rw [hp1,
                    the_tick_climbs_the_floor (t + 1) 1 (Nat.succ_le_succ (Nat.zero_le t))]
                  rfl
              | succ q₀ =>
                  have hp2 : rungs (t + 1) q₀ + t + 1 + 2 = p := by
                    rw [hq] at hrp
                    exact hrp
                  rw [← hp2]
                  exact the_sash_rests_above_a_tall_stair (t + 1) (rungs (t + 1) q₀ + t + 1)
            have hgb : groom s (t + 1) (s (t + p + 2)) = s (t + p + 1) := by
              show W s (t + 1) (s (t + p + 2))
                  - cond (sash (t + 1) (crank (t + 1) (s (t + p + 2) + 1))) 1 0
                = s (t + p + 1)
              rw [hsashb, the_family_beacon_slides t p s hg hf]
              rfl
            have hcoil : coil (W s (t + 1)) t (s (t + p + 1)) = s (p + 1) := by
              cases hq : (brand (t + 1) p).1 with
              | zero =>
                  have hp1 : p = 1 := by
                    rw [hq] at hrp
                    exact hrp.symm
                  subst hp1
                  show coil (W s (t + 1)) t (s (t + 2)) = s 2
                  rw [the_rail_reads_one t s hf, the_coil_rests_at_the_floor t s hf t]
                  exact (hf 1 (Nat.succ_le_succ (Nat.zero_le t))).symm
              | succ q₀ =>
                  have hp3 : rungs (t + 1) q₀ + t + 3 = p := by
                    rw [hq] at hrp
                    exact hrp
                  have hride := the_beacon_rides_the_coil t s hg hf t
                    (rungs (t + 1) q₀ + 2)
                  have hin : t + (rungs (t + 1) q₀ + 2) + t + 2 = t + p + 1 := by
                    rw [← hp3]
                    show t + rungs (t + 1) q₀ + 2 + t + 2
                      = t + (rungs (t + 1) q₀ + t) + 4
                    rw [Nat.add_assoc (t + rungs (t + 1) q₀) 2 t, Nat.add_comm 2 t,
                      ← Nat.add_assoc (t + rungs (t + 1) q₀) t 2,
                      ← Nat.add_assoc t (rungs (t + 1) q₀) t]
                  have hout : t + (rungs (t + 1) q₀ + 2) + 2 = p + 1 := by
                    rw [← hp3]
                    show t + rungs (t + 1) q₀ + 4 = rungs (t + 1) q₀ + t + 4
                    rw [Nat.add_comm t (rungs (t + 1) q₀)]
                  rw [hin, hout] at hride
                  exact hride
            have hbn1 : bride s (t + 1) (n + 1) = s (t + p + 2) := by
              show W s (t + 1) (n + 1)
                  + cond (veil (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0
                = s (t + p + 2)
              have hcv : crank (t + 1) (n + 1 + 1) = tick (t + 1) [p + 1] := by
                show tick (t + 1) (crank (t + 1) (n + 1)) = tick (t + 1) [p + 1]
                rw [hpage]
              have hveil : veil (t + 1) (tick (t + 1) [p + 1]) = false := by
                have h := the_veil_rests_above_a_tall_stair (t + 1)
                  (rungs (t + 1) (brand (t + 1) p).1)
                rw [show rungs (t + 1) (brand (t + 1) p).1 + 2 = p + 1 from
                  congrArg (· + 1) hrp] at h
                exact h
              have hW1 : W s (t + 1) (n + 1) = s (t + p + 2) := by
                rw [hn1]
                exact the_family_beacon_slides t (p + 1) s hg hf
              rw [hcv, hveil, hW1]
              rfl
            rw [hbn, hgb, hcoil, hbn1, hn1]
            show s (t + p + 2) + s (p + 1) = s (t + p + 3)
            exact (gnomon_tn t s hg p).symm
  | false =>
      have hbnf : bride s (t + 1) n = W s (t + 1) n := by
        show W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0
          = W s (t + 1) n
        rw [hv]
        rfl
      rw [hbnf]
      cases hs : sash (t + 1) (crank (t + 1) (W s (t + 1) n + 1)) with
      | false =>
          have hgf : groom s (t + 1) (W s (t + 1) n)
              = W s (t + 1) (W s (t + 1) n) := by
            show W s (t + 1) (W s (t + 1) n)
                - cond (sash (t + 1) (crank (t + 1) (W s (t + 1) n + 1))) 1 0 = _
            rw [hs]
            rfl
          rw [hgf]
          cases hb2 : veil (t + 1) (crank (t + 1) (n + 1 + 1)) with
          | false =>
              have hbn1 : bride s (t + 1) (n + 1) = W s (t + 1) (n + 1) := by
                show W s (t + 1) (n + 1)
                    + cond (veil (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0 = _
                rw [hb2]
                rfl
              rw [hbn1]
              exact the_family_loop_closes t s hg hf hz n
          | true =>
              cases the_veil_finds_its_beacon (t + 1) (crank (t + 1) (n + 1 + 1)) hb2 with
              | inl h0 =>
                  have h1 : n + 1 + 1 = s (t + 0 + 2) :=
                    a_crossing_reads_its_stair t s hg hf (n + 1) 0 h0
                  have h2 : n + 1 + 1 = 1 := by
                    rw [h1]
                    exact the_rail_reads_one t s hf
                  exact nomatch (Nat.succ.inj h2 : n + 1 = 0)
              | inr hex2 =>
                  match hex2 with
                  | ⟨p, hpage2, hres2⟩ =>
                    have hr1 : (brand (t + 1) p).2 = 1 := Nat.eq_of_beq_eq_true hres2
                    have hrp : rungs (t + 1) (brand (t + 1) p).1 + 1 = p := by
                      have h := the_brand_reads_the_rungs (t + 1) p
                      rw [hr1] at h
                      exact h
                    have hcn1 : crank (t + 1) (n + 1)
                        = 1 :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
                      rw [the_crank_steps_back (t + 1) (n + 1), hpage2]
                      show (brand (t + 1) p).2
                          :: unfurl (t + 1) (brand (t + 1) p).1 [] = _
                      rw [hr1]
                    cases hq : (brand (t + 1) p).1 with
                    | zero =>
                        rw [hq] at hcn1
                        have hcn1' : crank (t + 1) (n + 1) = [1] := hcn1
                        have hn1 : n + 1 = s (t + 1 + 2) :=
                          a_crossing_reads_its_stair t s hg hf n 1 hcn1'
                        have hn1' : n + 1 = 2 := by
                          rw [hn1]
                          exact the_first_flight_reads_two t s hg hf
                        have hn' : n = 1 := Nat.succ.inj hn1'
                        subst hn'
                        have hw1 : W s (t + 1) 1 = 1 := by
                          show s (t + 1 + 0) + 0 = 1
                          exact the_floor_reads_one t s hf
                        rw [hw1] at hs
                        exact nomatch hs
                    | succ q₀ =>
                        have hp3 : rungs (t + 1) q₀ + t + 3 = p := by
                          rw [hq] at hrp
                          exact hrp
                        have hcn0 : crank (t + 1) n
                            = 0 :: (t + 1 + 1) :: unfurl (t + 1) q₀ [] := by
                          rw [the_crank_steps_back (t + 1) n, hcn1, hq]
                          rfl
                        have hpu := a_purse_and_a_stair_make_a_beacon (t + 1) s hg q₀
                          (t + 1 + 1) (t + 1)
                        have hXY : s (t + 1 + (t + 1 + 1) + 2)
                            = s (t + 1 + (t + 1 + 1) + 1) + s (t + 3) := by
                          have h := hg (t + 2)
                          rw [Nat.add_comm (t + 2) (t + 1)] at h
                          exact h
                        rw [hXY, the_first_flight_reads_two t s hg hf] at hpu
                        rw [← Nat.add_assoc
                          (assay s (t + 1 + 1)
                            ((t + 1 + 1) :: unfurl (t + 1) q₀ []))
                          (s (t + 1 + (t + 1 + 1) + 1)) 2] at hpu
                        rw [add_swap_right
                          (assay s (t + 1 + 1)
                            ((t + 1 + 1) :: unfurl (t + 1) q₀ []))
                          (s (t + 1 + (t + 1 + 1) + 1)) 2] at hpu
                        have hA2 := unstack
                          (assay s (t + 1 + 1)
                            ((t + 1 + 1) :: unfurl (t + 1) q₀ []) + 2)
                          (s (t + 1 + rungs (t + 1) q₀ + (t + 1 + 1) + 2))
                          (s (t + 1 + (t + 1 + 1) + 1)) hpu
                        have hmid2 : t + 1 + rungs (t + 1) q₀ + (t + 1 + 1) + 2
                            = t + p + 2 := by
                          rw [← hp3]
                          show t + 1 + rungs (t + 1) q₀ + t + 4
                            = t + (rungs (t + 1) q₀ + t) + 5
                          rw [seat_shuffles t (rungs (t + 1) q₀),
                            seat_shuffles (t + rungs (t + 1) q₀) t,
                            ← Nat.add_assoc t (rungs (t + 1) q₀) t]
                        rw [hmid2] at hA2
                        have hVn : W s (t + 1) n + 1 = s (t + p + 2) := by
                          have hWn : W s (t + 1) n = s (t + 1)
                              + assay s (t + 1 + 1)
                                ((t + 1 + 1) :: unfurl (t + 1) q₀ []) := by
                            show assay s (t + 1) (crank (t + 1) n) = _
                            rw [hcn0]
                            rfl
                          rw [hWn, the_floor_reads_one t s hf,
                            Nat.add_comm 1 (assay s (t + 1 + 1)
                              ((t + 1 + 1) :: unfurl (t + 1) q₀ []))]
                          exact hA2
                        have hcb : crank (t + 1) (W s (t + 1) n + 1) = [p] := by
                          rw [hVn]
                          have h := the_crank_at_a_stair_number_is_one_stride (t + 1) p s hg hf
                          rw [seat_shuffles t p] at h
                          exact h
                        rw [hcb, ← hp3] at hs
                        have hsash : sash (t + 1) [rungs (t + 1) q₀ + t + 3] = true := by
                          show Nat.beq
                            (brand (t + 1) (rungs (t + 1) q₀ + t + 2)).2 0 = true
                          have hb' : brand (t + 1) (rungs (t + 1) q₀ + t + 2)
                              = (q₀ + 1, 0) := the_brand_mounts_the_rungs (t + 1) (q₀ + 1)
                          rw [hb']
                          rfl
                        exact nomatch (hsash.symm.trans hs)
      | true =>
          match the_sash_finds_its_beacon (t + 1)
            (crank (t + 1) (W s (t + 1) n + 1)) hs with
          | ⟨k, hpageW, hres0⟩ =>
            have hr0 : (brand (t + 1) k).2 = 0 := Nat.eq_of_beq_eq_true hres0
            have hrk : rungs (t + 1) (brand (t + 1) k).1 = k := by
              have h := the_brand_reads_the_rungs (t + 1) k
              rw [hr0] at h
              exact h
            have hcVn : crank (t + 1) (W s (t + 1) n)
                = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
              rw [the_crank_steps_back (t + 1) (W s (t + 1) n), hpageW]
              show (brand (t + 1) k).2 :: unfurl (t + 1) (brand (t + 1) k).1 [] = _
              rw [hr0]
            have hslip : slip (t + 1) (crank (t + 1) n)
                = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
              rw [← the_family_shadow_walks_the_slip t s hg hf n]
              exact hcVn
            cases hP : crank (t + 1) n with
            | nil =>
                rw [hP] at hslip
                exact nomatch hslip
            | cons g rest =>
              cases g with
              | succ g' =>
                  rw [hP] at hslip
                  injection hslip with hg0 hrest
                  subst hg0
                  subst hrest
                  have hcrn1 : crank (t + 1) (n + 1)
                      = [rungs (t + 1) (brand (t + 1) k).1 + 1 + 1] := by
                    show tick (t + 1) (crank (t + 1) n) = _
                    rw [hP]
                    have huntick : untick (t + 1)
                        [rungs (t + 1) (brand (t + 1) k).1 + 1 + 1]
                        = (0 + 1) :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
                      show (brand (t + 1)
                          (rungs (t + 1) (brand (t + 1) k).1 + 1)).2
                        :: unfurl (t + 1) (brand (t + 1)
                          (rungs (t + 1) (brand (t + 1) k).1 + 1)).1 [] = _
                      rw [the_brand_climbs_the_rungs (t + 1) (brand (t + 1) k).1 1
                        (Nat.succ_le_succ (Nat.zero_le t))]
                    rw [← huntick]
                    exact the_tick_comes_home (t + 1)
                      [rungs (t + 1) (brand (t + 1) k).1 + 1 + 1] True.intro
                      (fun h => nomatch h)
                  rw [hcrn1] at hv
                  have hveil : veil (t + 1)
                      [rungs (t + 1) (brand (t + 1) k).1 + 1 + 1] = true := by
                    show Nat.beq (brand (t + 1)
                        (rungs (t + 1) (brand (t + 1) k).1 + 1)).2 1 = true
                    rw [the_brand_climbs_the_rungs (t + 1) (brand (t + 1) k).1 1
                      (Nat.succ_le_succ (Nat.zero_le t))]
                    rfl
                  exact nomatch (hveil.symm.trans hv)
              | zero =>
                  rw [hP] at hslip
                  cases rest with
                  | nil =>
                      injection hslip with _ hqnil
                      cases hq : (brand (t + 1) k).1 with
                      | succ q₀ =>
                          rw [hq] at hqnil
                          exact nomatch hqnil
                      | zero =>
                          have hd' : s (t + 2) = n := by
                            have hd := the_dial_reads_true (t + 1) s hg hf n
                            rw [hP] at hd
                            exact hd
                          have hn' : n = 1 := by
                            rw [← hd']
                            exact the_rail_reads_one t s hf
                          subst hn'
                          have hw1 : W s (t + 1) 1 = 1 := by
                            show s (t + 1 + 0) + 0 = 1
                            exact the_floor_reads_one t s hf
                          have hg1 : groom s (t + 1) (W s (t + 1) 1) = 0 := by
                            rw [hw1]
                            show W s (t + 1) 1
                                - cond (sash (t + 1) (crank (t + 1) (1 + 1))) 1 0 = 0
                            rw [hw1]
                            rfl
                          have hcr3 : crank (t + 1) (1 + 1 + 1) = [2] := by
                            show tick (t + 1) (crank (t + 1) (1 + 1)) = [2]
                            exact the_tick_climbs_the_floor (t + 1) 1
                              (Nat.succ_le_succ (Nat.zero_le t))
                          have hb2v : bride s (t + 1) (1 + 1) = 1 + 1 := by
                            show W s (t + 1) (1 + 1)
                                + cond (veil (t + 1) (crank (t + 1) (1 + 1 + 1))) 1 0
                              = 1 + 1
                            rw [hcr3]
                            have hw2 : W s (t + 1) (1 + 1) = 1 := by
                              show s (t + 1 + 1 + 0) + 0 = 1
                              exact the_rail_reads_one t s hf
                            rw [hw2]
                            rfl
                          rw [hg1, the_coil_rests_at_zero t s t, hb2v]
                  | cons γ rest' =>
                      have hslip2 : cond (Nat.beq γ (t + 1))
                            (lift (t + 1 + 1) (perch (t + 1) rest'))
                            (0 :: (γ - 1) :: rest')
                          = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := hslip
                      cases hbq : Nat.beq γ (t + 1) with
                      | true =>
                          rw [hbq] at hslip2
                          cases hpr : perch (t + 1) rest' with
                          | nil => exact absurd hpr (the_perch_never_blanks (t + 1) rest')
                          | cons h0 hs0 =>
                              rw [hpr] at hslip2
                              injection hslip2 with hh _
                              exact nomatch hh
                      | false =>
                          rw [hbq] at hslip2
                          injection hslip2 with _ htail
                          cases hq : (brand (t + 1) k).1 with
                          | zero =>
                              rw [hq] at htail
                              exact nomatch htail
                          | succ q₀ =>
                              rw [hq] at htail
                              injection htail with hγ hrest'
                              cases γ with
                              | zero => exact nomatch hγ
                              | succ γ' =>
                                  have hγ'' : γ' = t + 1 := hγ
                                  subst hγ''
                                  subst hrest'
                                  rw [hq] at hrk
                                  have hVn1 : W s (t + 1) n + 1 = s (t + (k + 1) + 2) :=
                                    a_crossing_reads_its_stair t s hg hf
                                      (W s (t + 1) n) (k + 1) hpageW
                                  have hVVn : W s (t + 1) (W s (t + 1) n)
                                      = s (t + k + 2) := by
                                    have hpu' : assay s (t + 1)
                                          (0 :: unfurl (t + 1) (q₀ + 1) [])
                                          + s (t + 2)
                                        = s (t + rungs (t + 1) (q₀ + 1) + 0 + 2)
                                          + s (t + 1) :=
                                      a_purse_and_a_stair_make_a_beacon (t + 1) s hg
                                        (q₀ + 1) 0 t
                                    rw [the_rail_reads_one t s hf,
                                      the_floor_reads_one t s hf] at hpu'
                                    have hWVn : W s (t + 1) (W s (t + 1) n)
                                        = assay s (t + 1)
                                          (0 :: unfurl (t + 1) (q₀ + 1) []) := by
                                      show assay s (t + 1)
                                        (crank (t + 1) (W s (t + 1) n)) = _
                                      rw [hcVn, hq]
                                    rw [hWVn]
                                    have h' := unstack
                                      (assay s (t + 1) (0 :: unfurl (t + 1) (q₀ + 1) []))
                                      (s (t + rungs (t + 1) (q₀ + 1) + 0 + 2)) 1 hpu'
                                    rw [h']
                                    show s (t + rungs (t + 1) (q₀ + 1) + 2) = s (t + k + 2)
                                    rw [hrk]
                                  have hglow : 1 ≤ W s (t + 1) (W s (t + 1) n) := by
                                    show 1 ≤ assay s (t + 1)
                                      (crank (t + 1) (W s (t + 1) n))
                                    rw [hcVn]
                                    exact the_walk_glows_on_a_written_page t s hg hf 0
                                      (unfurl (t + 1) (brand (t + 1) k).1 [])
                                  have hgVn : groom s (t + 1) (W s (t + 1) n) + 1
                                      = s (t + k + 2) := by
                                    show (W s (t + 1) (W s (t + 1) n)
                                        - cond (sash (t + 1)
                                          (crank (t + 1) (W s (t + 1) n + 1))) 1 0) + 1
                                      = s (t + k + 2)
                                    rw [hs]
                                    show (W s (t + 1) (W s (t + 1) n) - 1) + 1
                                      = s (t + k + 2)
                                    rw [sub_one_back (W s (t + 1) (W s (t + 1) n)) hglow]
                                    exact hVVn
                                  have hkq : rungs (t + 1) q₀ + t + 2 = k := by
                                    rw [← hrk]
                                    rfl
                                  have hwound : coil (W s (t + 1)) t
                                        (groom s (t + 1) (W s (t + 1) n)) + 1
                                      = s (rungs (t + 1) q₀ + t + 4) := by
                                    apply the_wounded_beacon_rides_the_coil t s hg hf
                                      (rungs (t + 1) q₀ + t + 1)
                                      (groom s (t + 1) (W s (t + 1) n))
                                    · have hbb : brand (t + 1)
                                          (rungs (t + 1) q₀ + (t + 1)) = (q₀, t + 1) :=
                                        the_brand_climbs_the_rungs (t + 1) q₀ (t + 1)
                                          (Nat.le_refl (t + 1))
                                      show (brand (t + 1)
                                        (rungs (t + 1) q₀ + (t + 1))).2 = t + 1
                                      rw [hbb]
                                    · rw [hgVn]
                                      show s (t + k + 2)
                                        = s (rungs (t + 1) q₀ + t + 1 + t + 3)
                                      rw [← hkq]
                                      show s (t + (rungs (t + 1) q₀ + t + 2) + 2)
                                        = s (rungs (t + 1) q₀ + t + 1 + t + 3)
                                      have hidx : t + (rungs (t + 1) q₀ + t + 2) + 2
                                          = rungs (t + 1) q₀ + t + 1 + t + 3 := by
                                        show t + (rungs (t + 1) q₀ + t) + 4
                                          = rungs (t + 1) q₀ + t + 1 + t + 3
                                        rw [seat_shuffles (rungs (t + 1) q₀ + t) t,
                                          ← Nat.add_assoc t (rungs (t + 1) q₀) t,
                                          Nat.add_comm (rungs (t + 1) q₀) t]
                                      rw [hidx]
                                  have hcrn1 : crank (t + 1) (n + 1)
                                      = 1 :: unfurl (t + 1) (q₀ + 1) [] := by
                                    show tick (t + 1) (crank (t + 1) n) = _
                                    rw [hP]
                                    show lift 1 (perch (t + 1)
                                        ((t + 1 + 1) :: unfurl (t + 1) q₀ []))
                                      = 1 :: unfurl (t + 1) (q₀ + 1) []
                                    have hpq : perch (t + 1)
                                        ((t + 1 + 1) :: unfurl (t + 1) q₀ [])
                                        = 0 :: (t + 1) :: unfurl (t + 1) q₀ [] := by
                                      show cond (Nat.beq (t + 1 + 1) (t + 1))
                                          (lift (t + 1 + 1) (perch (t + 1)
                                            (unfurl (t + 1) q₀ [])))
                                          (0 :: (t + 1 + 1 - 1) :: unfurl (t + 1) q₀ [])
                                        = 0 :: (t + 1) :: unfurl (t + 1) q₀ []
                                      rw [beq_shuts_high (t + 1) (t + 1 + 1)
                                        (Nat.le_refl (t + 1 + 1))]
                                      rfl
                                    rw [hpq]
                                    rfl
                                  have hveil2 : veil (t + 1)
                                      (crank (t + 1) (n + 1 + 1)) = true := by
                                    have hct : crank (t + 1) (n + 1 + 1)
                                        = [rungs (t + 1) (q₀ + 1) + 1 + 1] := by
                                      show tick (t + 1) (crank (t + 1) (n + 1)) = _
                                      rw [hcrn1]
                                      have huntick : untick (t + 1)
                                          [rungs (t + 1) (q₀ + 1) + 1 + 1]
                                          = 1 :: unfurl (t + 1) (q₀ + 1) [] := by
                                        show (brand (t + 1)
                                            (rungs (t + 1) (q₀ + 1) + 1)).2
                                          :: unfurl (t + 1) (brand (t + 1)
                                            (rungs (t + 1) (q₀ + 1) + 1)).1 [] = _
                                        rw [the_brand_climbs_the_rungs (t + 1) (q₀ + 1) 1
                                          (Nat.succ_le_succ (Nat.zero_le t))]
                                      rw [← huntick]
                                      exact the_tick_comes_home (t + 1)
                                        [rungs (t + 1) (q₀ + 1) + 1 + 1] True.intro
                                        (fun h => nomatch h)
                                    rw [hct]
                                    show Nat.beq (brand (t + 1)
                                        (rungs (t + 1) (q₀ + 1) + 1)).2 1 = true
                                    rw [the_brand_climbs_the_rungs (t + 1) (q₀ + 1) 1
                                      (Nat.succ_le_succ (Nat.zero_le t))]
                                    rfl
                                  have hVnn : W s (t + 1) (n + 1) + 1
                                      = s (t + rungs (t + 1) (q₀ + 1) + 3) := by
                                    have hpu' : assay s (t + 1)
                                          (1 :: unfurl (t + 1) (q₀ + 1) []) + s (t + 3)
                                        = s (t + rungs (t + 1) (q₀ + 1) + 1 + 2)
                                          + s (t + 2) :=
                                      a_purse_and_a_stair_make_a_beacon (t + 1) s hg
                                        (q₀ + 1) 1 t
                                    rw [the_first_flight_reads_two t s hg hf,
                                      the_rail_reads_one t s hf] at hpu'
                                    have hWn1 : W s (t + 1) (n + 1)
                                        = assay s (t + 1)
                                          (1 :: unfurl (t + 1) (q₀ + 1) []) := by
                                      show assay s (t + 1) (crank (t + 1) (n + 1)) = _
                                      rw [hcrn1]
                                    rw [hWn1]
                                    have h' := Nat.succ.inj hpu'
                                    rw [h']
                                  have hn2 : n + 1 + 1
                                      = s (t + rungs (t + 1) (q₀ + 1) + 4) := by
                                    have hpu' : assay s (t + 1 + 1)
                                          (1 :: unfurl (t + 1) (q₀ + 1) [])
                                          + s (t + 1 + 1 + 2)
                                        = s (t + 1 + rungs (t + 1) (q₀ + 1) + 1 + 2)
                                          + s (t + 1 + 1 + 1) :=
                                      a_purse_and_a_stair_make_a_beacon (t + 1) s hg
                                        (q₀ + 1) 1 (t + 1)
                                    have hpu'' : assay s (t + 1 + 1)
                                          (1 :: unfurl (t + 1) (q₀ + 1) []) + s (t + 4)
                                        = s (t + 1 + rungs (t + 1) (q₀ + 1) + 1 + 2)
                                          + s (t + 3) := hpu'
                                    rw [the_second_flight_reads_three t s hg hf,
                                      the_first_flight_reads_two t s hg hf] at hpu''
                                    have hdn : assay s (t + 1 + 1)
                                        (1 :: unfurl (t + 1) (q₀ + 1) []) = n + 1 := by
                                      have hd := the_dial_reads_true (t + 1) s hg hf (n + 1)
                                      rw [hcrn1] at hd
                                      exact hd
                                    rw [hdn] at hpu''
                                    have hmid3 : t + 1 + rungs (t + 1) (q₀ + 1) + 1 + 2
                                        = t + rungs (t + 1) (q₀ + 1) + 4 := by
                                      rw [seat_shuffles t (rungs (t + 1) (q₀ + 1))]
                                    rw [hmid3] at hpu''
                                    have h3 : (n + 1 + 1) + 2
                                        = s (t + rungs (t + 1) (q₀ + 1) + 4) + 2 := hpu''
                                    exact unstack (n + 1 + 1)
                                      (s (t + rungs (t + 1) (q₀ + 1) + 4)) 2 h3
                                  have hbb1 : bride s (t + 1) (n + 1)
                                      = W s (t + 1) (n + 1) + 1 := by
                                    show W s (t + 1) (n + 1)
                                        + cond (veil (t + 1)
                                          (crank (t + 1) (n + 1 + 1))) 1 0
                                      = W s (t + 1) (n + 1) + 1
                                    rw [hveil2]
                                    rfl
                                  rw [hbb1]
                                  have hsum : (W s (t + 1) (n + 1) + 1
                                        + coil (W s (t + 1)) t
                                          (groom s (t + 1) (W s (t + 1) n))) + 1
                                      = n + 1 + 1 := by
                                    rw [Nat.add_assoc (W s (t + 1) (n + 1) + 1)
                                      (coil (W s (t + 1)) t
                                        (groom s (t + 1) (W s (t + 1) n))) 1,
                                      hwound]
                                    rw [hn2]
                                    have hgnm := gnomon_tn t s hg
                                      (rungs (t + 1) (q₀ + 1) + 1)
                                    have hgnm' : s (t + rungs (t + 1) (q₀ + 1) + 4)
                                        = s (t + rungs (t + 1) (q₀ + 1) + 3)
                                          + s (rungs (t + 1) (q₀ + 1) + 2) := hgnm
                                    rw [hgnm', ← hVnn]
                                    show W s (t + 1) (n + 1) + 1
                                        + s (rungs (t + 1) q₀ + t + 4)
                                      = W s (t + 1) (n + 1) + 1
                                        + s (rungs (t + 1) (q₀ + 1) + 2)
                                    rfl
                                  exact Nat.succ.inj hsum

/-- info: 'Foam.Bridges.the_family_marriage_closes_for_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_marriage_closes_for_the_bride

theorem the_coil_winds_outward (t : Nat) (s : Nat → Nat) :
    ∀ (j x : Nat), W s (t + 1) (coil (W s (t + 1)) j x)
      = coil (W s (t + 1)) j (W s (t + 1) x)
  | 0, _ => rfl
  | j + 1, x => the_coil_winds_outward t s j (W s (t + 1) x)

theorem the_family_stays_awake (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat) : 1 ≤ W s (t + 1) (n + 1) := by
  cases hc : crank (t + 1) (n + 1) with
  | nil => exact absurd hc (the_tick_never_blanks (t + 1) (crank (t + 1) n))
  | cons g gs =>
      show 1 ≤ assay s (t + 1) (crank (t + 1) (n + 1))
      rw [hc]
      exact the_walk_glows_on_a_written_page t s hg hf g gs

theorem the_low_seat_glows (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (g : Nat) (gs : List Nat) :
    1 ≤ assay s (0 + 1) (g :: gs) := by
  show 1 ≤ s (0 + 1 + g) + assay s (0 + 1 + g + 1) gs
  rw [Nat.zero_add 1, Nat.add_comm 1 g]
  exact Nat.le_trans (a_grammar_glows (t + 1) s hg hf g)
    (Nat.le_add_right (s (g + 1)) (assay s (g + 1 + 1) gs))

/-- info: 'Foam.Bridges.the_coil_winds_outward' does not depend on any axioms -/
#guard_msgs in #print axioms the_coil_winds_outward

/-- info: 'Foam.Bridges.the_family_stays_awake' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_stays_awake

/-- info: 'Foam.Bridges.the_low_seat_glows' does not depend on any axioms -/
#guard_msgs in #print axioms the_low_seat_glows

theorem the_slip_reads_back (t : Nat) : ∀ (gs : List Nat) (h : Nat) (rest : List Nat),
    h + 1 ≤ t + 1 → slip (t + 1) gs = (h + 1) :: rest → gs = (h + 2) :: rest
  | [], _, _, _, heq => nomatch heq
  | (g + 1) :: gs', h, rest, _, heq => by
      have heq' : g :: gs' = (h + 1) :: rest := heq
      injection heq' with h1 h2
      rw [h1, h2]
  | 0 :: gs', h, rest, hle, heq => by
      cases gs' with
      | nil =>
          have heq' : [0] = (h + 1) :: rest := heq
          injection heq' with h1 _
          exact nomatch h1
      | cons γ r =>
          have heq2 : cond (Nat.beq γ (t + 1))
              (lift (t + 1 + 1) (perch (t + 1) r)) (0 :: (γ - 1) :: r)
            = (h + 1) :: rest := heq
          cases hbq : Nat.beq γ (t + 1) with
          | true =>
              rw [hbq] at heq2
              cases hpr : perch (t + 1) r with
              | nil => exact absurd hpr (the_perch_never_blanks (t + 1) r)
              | cons x xs =>
                  rw [hpr] at heq2
                  injection heq2 with hx _
                  have hge : t + 1 + 1 ≤ h + 1 := by
                    rw [← hx]
                    exact Nat.le_add_left (t + 1 + 1) x
                  exact absurd (Nat.le_trans hge hle) (Nat.not_succ_le_self (t + 1))
          | false =>
              rw [hbq] at heq2
              injection heq2 with h1 _
              exact nomatch h1

/-- info: 'Foam.Bridges.the_slip_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_slip_reads_back

theorem the_shadow_climbs_back (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (j x h : Nat) (rest : List Nat),
      h + 1 + j ≤ t + 1 →
      crank (t + 1) (coil (W s (t + 1)) (j + 1) x) = (h + 1) :: rest →
      crank (t + 1) x = (h + j + 2) :: rest
  | 0, x, h, rest, hle, heq => by
      have hsl : slip (t + 1) (crank (t + 1) x) = (h + 1) :: rest := by
        rw [← the_family_shadow_walks_the_slip t s hg hf x]
        exact heq
      exact the_slip_reads_back t (crank (t + 1) x) h rest hle hsl
  | j + 1, x, h, rest, hle, heq => by
      have hle2 : h + 1 + j + 1 ≤ t + 1 := hle
      have hihle : h + 1 + j ≤ t + 1 := Nat.le_of_succ_le hle2
      have hih := the_shadow_climbs_back t s hg hf j (W s (t + 1) x) h rest hihle heq
      have hsl : slip (t + 1) (crank (t + 1) x) = (h + j + 1 + 1) :: rest := by
        rw [← the_family_shadow_walks_the_slip t s hg hf x]
        exact hih
      have hle3 : h + j + 1 + 1 ≤ t + 1 := by
        rw [← seat_shuffles h j]
        exact hle2
      exact the_slip_reads_back t (crank (t + 1) x) (h + j + 1) rest hle3 hsl

/-- info: 'Foam.Bridges.the_shadow_climbs_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_shadow_climbs_back

theorem the_family_marriage_closes_for_the_groom (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    groom s (t + 1) (n + 1)
      + bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)) = n + 1 := by
  cases hσ : sash (t + 1) (crank (t + 1) (n + 1)) with
  | true =>
      match the_sash_finds_its_beacon (t + 1) (crank (t + 1) (n + 1)) hσ with
      | ⟨k, hpage, hres0⟩ =>
        have hr0 : (brand (t + 1) k).2 = 0 := Nat.eq_of_beq_eq_true hres0
        have hrk : rungs (t + 1) (brand (t + 1) k).1 = k := by
          have h := the_brand_reads_the_rungs (t + 1) k
          rw [hr0] at h
          exact h
        have hn1 : n + 1 = s (t + (k + 1) + 2) :=
          a_crossing_reads_its_stair t s hg hf n (k + 1) hpage
        have hcn : crank (t + 1) n = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
          rw [the_crank_steps_back (t + 1) n, hpage]
          show (brand (t + 1) k).2 :: unfurl (t + 1) (brand (t + 1) k).1 [] = _
          rw [hr0]
        have hWn : W s (t + 1) n = s (t + k + 2) := by
          have hpu' : assay s (t + 1) (0 :: unfurl (t + 1) (brand (t + 1) k).1 [])
                + s (t + 2)
              = s (t + rungs (t + 1) (brand (t + 1) k).1 + 0 + 2) + s (t + 1) :=
            a_purse_and_a_stair_make_a_beacon (t + 1) s hg (brand (t + 1) k).1 0 t
          rw [the_rail_reads_one t s hf, the_floor_reads_one t s hf] at hpu'
          have hW : W s (t + 1) n
              = assay s (t + 1) (0 :: unfurl (t + 1) (brand (t + 1) k).1 []) := by
            show assay s (t + 1) (crank (t + 1) n) = _
            rw [hcn]
          rw [hW]
          have h' := unstack
            (assay s (t + 1) (0 :: unfurl (t + 1) (brand (t + 1) k).1 []))
            (s (t + rungs (t + 1) (brand (t + 1) k).1 + 0 + 2)) 1 hpu'
          rw [h']
          show s (t + rungs (t + 1) (brand (t + 1) k).1 + 2) = s (t + k + 2)
          rw [hrk]
        have hgroomn : groom s (t + 1) n + 1 = s (t + k + 2) := by
          show (W s (t + 1) n - cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0) + 1
            = s (t + k + 2)
          rw [hσ]
          show (W s (t + 1) n - 1) + 1 = s (t + k + 2)
          have hglow : 1 ≤ W s (t + 1) n := by
            show 1 ≤ assay s (t + 1) (crank (t + 1) n)
            rw [hcn]
            exact the_walk_glows_on_a_written_page t s hg hf 0
              (unfurl (t + 1) (brand (t + 1) k).1 [])
          rw [sub_one_back (W s (t + 1) n) hglow]
          exact hWn
        cases hq : (brand (t + 1) k).1 with
        | zero =>
            have hk0 : k = 0 := by
              rw [hq] at hrk
              exact hrk.symm
            subst hk0
            have hn1' : n + 1 = 2 := by
              rw [hn1]
              exact the_first_flight_reads_two t s hg hf
            have hn' : n = 1 := Nat.succ.inj hn1'
            subst hn'
            have hw1 : W s (t + 1) 1 = 1 := by
              show s (t + 1 + 0) + 0 = 1
              exact the_floor_reads_one t s hf
            have hg1 : groom s (t + 1) 1 = 0 := by
              show W s (t + 1) 1 - cond (sash (t + 1) (crank (t + 1) (1 + 1))) 1 0 = 0
              rw [hw1]
              rfl
            rw [hg1, the_coil_rests_at_zero t s t]
            have hcr3 : crank (t + 1) (1 + 1 + 1) = [2] := by
              show tick (t + 1) (crank (t + 1) (1 + 1)) = [2]
              exact the_tick_climbs_the_floor (t + 1) 1 (Nat.succ_le_succ (Nat.zero_le t))
            have hg2 : groom s (t + 1) (1 + 1) = 1 := by
              show W s (t + 1) (1 + 1)
                  - cond (sash (t + 1) (crank (t + 1) (1 + 1 + 1))) 1 0 = 1
              rw [hcr3]
              have hw2 : W s (t + 1) (1 + 1) = 1 := by
                show s (t + 1 + 1 + 0) + 0 = 1
                exact the_rail_reads_one t s hf
              rw [hw2]
              rfl
            rw [hg2]
            rfl
        | succ q₀ =>
            have hkq : rungs (t + 1) q₀ + t + 2 = k := by
              rw [hq] at hrk
              exact hrk
            have hwound : coil (W s (t + 1)) t (groom s (t + 1) n) + 1
                = s (rungs (t + 1) q₀ + t + 4) := by
              apply the_wounded_beacon_rides_the_coil t s hg hf
                (rungs (t + 1) q₀ + t + 1) (groom s (t + 1) n)
              · have hbb : brand (t + 1) (rungs (t + 1) q₀ + (t + 1)) = (q₀, t + 1) :=
                  the_brand_climbs_the_rungs (t + 1) q₀ (t + 1) (Nat.le_refl (t + 1))
                show (brand (t + 1) (rungs (t + 1) q₀ + (t + 1))).2 = t + 1
                rw [hbb]
              · rw [hgroomn]
                show s (t + k + 2) = s (rungs (t + 1) q₀ + t + 1 + t + 3)
                rw [← hkq]
                have hidx : t + (rungs (t + 1) q₀ + t + 2) + 2
                    = rungs (t + 1) q₀ + t + 1 + t + 3 := by
                  show t + (rungs (t + 1) q₀ + t) + 4
                    = rungs (t + 1) q₀ + t + 1 + t + 3
                  rw [seat_shuffles (rungs (t + 1) q₀ + t) t,
                    ← Nat.add_assoc t (rungs (t + 1) q₀) t,
                    Nat.add_comm (rungs (t + 1) q₀) t]
                rw [hidx]
            have hcrch : crank (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n) + 1)
                = [rungs (t + 1) q₀ + 2] := by
              have h := the_crank_at_a_stair_number_is_one_stride (t + 1)
                (rungs (t + 1) q₀ + 2) s hg hf
              have hidx2 : t + 1 + (rungs (t + 1) q₀ + 2) + 1
                  = rungs (t + 1) q₀ + t + 4 := by
                show t + 1 + rungs (t + 1) q₀ + 3 = rungs (t + 1) q₀ + t + 4
                rw [seat_shuffles t (rungs (t + 1) q₀),
                  Nat.add_comm t (rungs (t + 1) q₀)]
              rw [hidx2] at h
              rw [hwound]
              exact h
            have hcch : crank (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n))
                = 1 :: unfurl (t + 1) q₀ [] := by
              rw [the_crank_steps_back (t + 1)
                (coil (W s (t + 1)) t (groom s (t + 1) n)), hcrch]
              show (brand (t + 1) (rungs (t + 1) q₀ + 1)).2
                  :: unfurl (t + 1) (brand (t + 1) (rungs (t + 1) q₀ + 1)).1 [] = _
              rw [the_brand_climbs_the_rungs (t + 1) q₀ 1
                (Nat.succ_le_succ (Nat.zero_le t))]
            have hWch : W s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)) + 1
                = s (t + rungs (t + 1) q₀ + 3) := by
              have hpu' : assay s (t + 1) (1 :: unfurl (t + 1) q₀ []) + s (t + 3)
                  = s (t + rungs (t + 1) q₀ + 1 + 2) + s (t + 2) :=
                a_purse_and_a_stair_make_a_beacon (t + 1) s hg q₀ 1 t
              rw [the_first_flight_reads_two t s hg hf, the_rail_reads_one t s hf] at hpu'
              have hW : W s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n))
                  = assay s (t + 1) (1 :: unfurl (t + 1) q₀ []) := by
                show assay s (t + 1)
                  (crank (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n))) = _
                rw [hcch]
              rw [hW]
              exact Nat.succ.inj hpu'
            have hbridech : bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n))
                = s (t + rungs (t + 1) q₀ + 3) := by
              show W s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n))
                  + cond (veil (t + 1) (crank (t + 1)
                    (coil (W s (t + 1)) t (groom s (t + 1) n) + 1))) 1 0
                = s (t + rungs (t + 1) q₀ + 3)
              rw [hcrch]
              have hveilch : veil (t + 1) [rungs (t + 1) q₀ + 2] = true := by
                show Nat.beq (brand (t + 1) (rungs (t + 1) q₀ + 1)).2 1 = true
                rw [the_brand_climbs_the_rungs (t + 1) q₀ 1
                  (Nat.succ_le_succ (Nat.zero_le t))]
                rfl
              rw [hveilch]
              exact hWch
            have hWn1 : W s (t + 1) (n + 1) = s (t + k + 2) := by
              rw [hn1]
              exact the_family_beacon_slides t (k + 1) s hg hf
            have hsashn2 : sash (t + 1) (crank (t + 1) (n + 1 + 1)) = false := by
              have hct : crank (t + 1) (n + 1 + 1) = tick (t + 1) [k + 1] := by
                show tick (t + 1) (crank (t + 1) (n + 1)) = tick (t + 1) [k + 1]
                rw [hpage]
              rw [hct]
              have hk1 : k + 1 = rungs (t + 1) q₀ + t + 1 + 2 := by
                rw [← hkq]
              rw [hk1]
              exact the_sash_rests_above_a_tall_stair (t + 1) (rungs (t + 1) q₀ + t + 1)
            have hgn1 : groom s (t + 1) (n + 1) = s (t + k + 2) := by
              show W s (t + 1) (n + 1)
                  - cond (sash (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0 = s (t + k + 2)
              rw [hsashn2, hWn1]
              rfl
            rw [hgn1, hbridech, hn1]
            show s (t + k + 2) + s (t + rungs (t + 1) q₀ + 3) = s (t + k + 3)
            have hkk : t + rungs (t + 1) q₀ + 3 = k + 1 := by
              rw [← hkq]
              show t + rungs (t + 1) q₀ + 3 = rungs (t + 1) q₀ + t + 3
              rw [Nat.add_comm t (rungs (t + 1) q₀)]
            rw [hkk]
            exact (gnomon_tn t s hg k).symm
  | false =>
      have hgnf : groom s (t + 1) n = W s (t + 1) n := by
        show W s (t + 1) n - cond (sash (t + 1) (crank (t + 1) (n + 1))) 1 0
          = W s (t + 1) n
        rw [hσ]
        rfl
      rw [hgnf]
      cases hgn2 : sash (t + 1) (crank (t + 1) (n + 1 + 1)) with
      | false =>
          cases hb : veil (t + 1)
            (crank (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n) + 1)) with
          | false =>
              have hbch : bride s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))
                  = W s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n)) := by
                show W s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))
                    + cond (veil (t + 1) (crank (t + 1)
                      (coil (W s (t + 1)) t (W s (t + 1) n) + 1))) 1 0 = _
                rw [hb]
                rfl
              have hgn1f : groom s (t + 1) (n + 1) = W s (t + 1) (n + 1) := by
                show W s (t + 1) (n + 1)
                    - cond (sash (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0 = _
                rw [hgn2]
                rfl
              rw [hgn1f, hbch, the_coil_winds_outward t s t (W s (t + 1) n)]
              exact the_family_loop_closes t s hg hf hz n
          | true =>
              cases the_veil_finds_its_beacon (t + 1)
                (crank (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n) + 1)) hb with
              | inl h0 =>
                  have hch1 : coil (W s (t + 1)) t (W s (t + 1) n) + 1
                      = s (t + 0 + 2) :=
                    a_crossing_reads_its_stair t s hg hf
                      (coil (W s (t + 1)) t (W s (t + 1) n)) 0 h0
                  have hch1' : coil (W s (t + 1)) t (W s (t + 1) n) + 1 = 1 := by
                    rw [hch1]
                    exact the_rail_reads_one t s hf
                  have hch0 : coil (W s (t + 1)) t (W s (t + 1) n) = 0 :=
                    Nat.succ.inj hch1'
                  have hsh := the_shadows_descend t s hg hf t 0 n
                    (congrArg (· + 1) (Nat.zero_add t))
                  cases hP : crank (t + 1) n with
                  | cons g gs =>
                      have hglow : 1 ≤ assay s (0 + 1) (crank (t + 1) n) := by
                        rw [hP]
                        exact the_low_seat_glows t s hg hf g gs
                      rw [← hsh] at hglow
                      have hglow' : 1 ≤ coil (W s (t + 1)) t (W s (t + 1) n) := hglow
                      rw [hch0] at hglow'
                      exact absurd hglow' (Nat.not_succ_le_zero 0)
                  | nil =>
                      have hd : assay s (t + 1 + 1) (crank (t + 1) n) = n :=
                        the_dial_reads_true (t + 1) s hg hf n
                      rw [hP] at hd
                      rw [← hd] at hgn2
                      exact nomatch hgn2
              | inr hex =>
                  match hex with
                  | ⟨j, hpagec, hresc⟩ =>
                    have hr1 : (brand (t + 1) j).2 = 1 := Nat.eq_of_beq_eq_true hresc
                    have hcch : crank (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))
                        = 1 :: unfurl (t + 1) (brand (t + 1) j).1 [] := by
                      rw [the_crank_steps_back (t + 1)
                        (coil (W s (t + 1)) t (W s (t + 1) n)), hpagec]
                      show (brand (t + 1) j).2
                          :: unfurl (t + 1) (brand (t + 1) j).1 [] = _
                      rw [hr1]
                    have hpin : crank (t + 1) n
                        = (0 + t + 2) :: unfurl (t + 1) (brand (t + 1) j).1 [] := by
                      apply the_shadow_climbs_back t s hg hf t n 0
                        (unfurl (t + 1) (brand (t + 1) j).1 [])
                      · show 0 + 1 + t ≤ t + 1
                        rw [Nat.zero_add 1, Nat.add_comm 1 t]
                        exact Nat.le_refl (t + 1)
                      · exact hcch
                    have hpin' : crank (t + 1) n
                        = (t + 1 + 1) :: unfurl (t + 1) (brand (t + 1) j).1 [] := by
                      rw [hpin]
                      show (0 + t + 2) :: unfurl (t + 1) (brand (t + 1) j).1 []
                        = (t + 1 + 1) :: unfurl (t + 1) (brand (t + 1) j).1 []
                      rw [Nat.zero_add t]
                    have hpu := a_purse_and_a_stair_make_a_beacon (t + 1) s hg
                      (brand (t + 1) j).1 (t + 1 + 1) (t + 1)
                    have hXY : s (t + 1 + (t + 1 + 1) + 2)
                        = s (t + 1 + (t + 1 + 1) + 1) + s (t + 3) := by
                      have h := hg (t + 2)
                      rw [Nat.add_comm (t + 2) (t + 1)] at h
                      exact h
                    rw [hXY, the_first_flight_reads_two t s hg hf] at hpu
                    rw [← Nat.add_assoc
                      (assay s (t + 1 + 1)
                        ((t + 1 + 1) :: unfurl (t + 1) (brand (t + 1) j).1 []))
                      (s (t + 1 + (t + 1 + 1) + 1)) 2] at hpu
                    rw [add_swap_right
                      (assay s (t + 1 + 1)
                        ((t + 1 + 1) :: unfurl (t + 1) (brand (t + 1) j).1 []))
                      (s (t + 1 + (t + 1 + 1) + 1)) 2] at hpu
                    have hA2 := unstack
                      (assay s (t + 1 + 1)
                        ((t + 1 + 1) :: unfurl (t + 1) (brand (t + 1) j).1 []) + 2)
                      (s (t + 1 + rungs (t + 1) (brand (t + 1) j).1 + (t + 1 + 1) + 2))
                      (s (t + 1 + (t + 1 + 1) + 1)) hpu
                    have hdn : assay s (t + 1 + 1)
                        ((t + 1 + 1) :: unfurl (t + 1) (brand (t + 1) j).1 []) = n := by
                      have hd := the_dial_reads_true (t + 1) s hg hf n
                      rw [hpin'] at hd
                      exact hd
                    rw [hdn] at hA2
                    have hcr2 : crank (t + 1) (n + 1 + 1)
                        = [rungs (t + 1) (brand (t + 1) j).1 + t + 3] := by
                      have h := the_crank_at_a_stair_number_is_one_stride (t + 1)
                        (rungs (t + 1) (brand (t + 1) j).1 + t + 3) s hg hf
                      have hidx : t + 1 + (rungs (t + 1) (brand (t + 1) j).1 + t + 3) + 1
                          = t + 1 + rungs (t + 1) (brand (t + 1) j).1 + (t + 1 + 1) + 2 := by
                        show t + 1 + (rungs (t + 1) (brand (t + 1) j).1 + t) + 4
                          = t + 1 + rungs (t + 1) (brand (t + 1) j).1 + t + 4
                        rw [← Nat.add_assoc (t + 1) (rungs (t + 1) (brand (t + 1) j).1) t]
                      rw [hidx] at h
                      rw [← hA2] at h
                      exact h
                    have hsash2 : sash (t + 1)
                        [rungs (t + 1) (brand (t + 1) j).1 + t + 3] = true := by
                      show Nat.beq (brand (t + 1)
                          (rungs (t + 1) (brand (t + 1) j).1 + t + 2)).2 0 = true
                      have hb' : brand (t + 1)
                          (rungs (t + 1) ((brand (t + 1) j).1 + 1)) = ((brand (t + 1) j).1 + 1, 0) :=
                        the_brand_mounts_the_rungs (t + 1) ((brand (t + 1) j).1 + 1)
                      have hb'' : brand (t + 1)
                          (rungs (t + 1) (brand (t + 1) j).1 + t + 2)
                          = ((brand (t + 1) j).1 + 1, 0) := hb'
                      rw [hb'']
                      rfl
                    rw [hcr2] at hgn2
                    exact nomatch (hsash2.symm.trans hgn2)
      | true =>
          match the_sash_finds_its_beacon (t + 1) (crank (t + 1) (n + 1 + 1)) hgn2 with
          | ⟨k, hpage2, hres0⟩ =>
            have hr0 : (brand (t + 1) k).2 = 0 := Nat.eq_of_beq_eq_true hres0
            have hrk : rungs (t + 1) (brand (t + 1) k).1 = k := by
              have h := the_brand_reads_the_rungs (t + 1) k
              rw [hr0] at h
              exact h
            have hcn1 : crank (t + 1) (n + 1)
                = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
              rw [the_crank_steps_back (t + 1) (n + 1), hpage2]
              show (brand (t + 1) k).2 :: unfurl (t + 1) (brand (t + 1) k).1 [] = _
              rw [hr0]
            cases hq : (brand (t + 1) k).1 with
            | zero =>
                rw [hq] at hcn1
                have hd : assay s (t + 1 + 1) (crank (t + 1) (n + 1)) = n + 1 :=
                  the_dial_reads_true (t + 1) s hg hf (n + 1)
                rw [hcn1] at hd
                have hd' : s (t + 2) = n + 1 := hd
                have hn0 : n + 1 = 1 := by
                  rw [← hd']
                  exact the_rail_reads_one t s hf
                have hn0' : n = 0 := Nat.succ.inj hn0
                subst hn0'
                have hw1 : W s (t + 1) 1 = 1 := by
                  show s (t + 1 + 0) + 0 = 1
                  exact the_floor_reads_one t s hf
                have hg1 : groom s (t + 1) (0 + 1) = 0 := by
                  show W s (t + 1) 1 - cond (sash (t + 1) (crank (t + 1) (1 + 1))) 1 0 = 0
                  rw [hw1]
                  rfl
                rw [hg1]
                show 0 + bride s (t + 1) (coil (W s (t + 1)) t 0) = 0 + 1
                rw [the_coil_rests_at_zero t s t]
                rfl
            | succ q₀ =>
                have hcn0 : crank (t + 1) n
                    = (t + 1 + 1) :: unfurl (t + 1) q₀ [] := by
                  rw [the_crank_steps_back (t + 1) n, hcn1, hq]
                  rfl
                have hkq : rungs (t + 1) q₀ + t + 2 = k := by
                  rw [hq] at hrk
                  exact hrk
                have hsh := the_shadows_descend t s hg hf t 0 n
                  (congrArg (· + 1) (Nat.zero_add t))
                have hpu' : assay s (0 + 1) ((t + 1 + 1) :: unfurl (t + 1) q₀ [])
                      + s (0 + (t + 1 + 1) + 2)
                    = s (0 + rungs (t + 1) q₀ + (t + 1 + 1) + 2)
                      + s (0 + (t + 1 + 1) + 1) :=
                  a_purse_and_a_stair_make_a_beacon (t + 1) s hg q₀ (t + 1 + 1) 0
                have hpu'' : assay s (0 + 1) ((t + 1 + 1) :: unfurl (t + 1) q₀ [])
                      + s (t + 1 + 3)
                    = s (0 + rungs (t + 1) q₀ + (t + 1 + 1) + 2) + s (t + 1 + 2) := by
                  have h1 : (0 : Nat) + (t + 1 + 1) + 2 = t + 1 + 3 := by
                    rw [Nat.zero_add (t + 1 + 1)]
                  have h2 : (0 : Nat) + (t + 1 + 1) + 1 = t + 1 + 2 := by
                    rw [Nat.zero_add (t + 1 + 1)]
                  rw [h1, h2] at hpu'
                  exact hpu'
                rw [the_second_flight_reads_three t s hg hf,
                  the_first_flight_reads_two t s hg hf] at hpu''
                have hchain : coil (W s (t + 1)) t (W s (t + 1) n) + 1
                    = s (rungs (t + 1) q₀ + t + 4) := by
                  have hchsh : coil (W s (t + 1)) t (W s (t + 1) n)
                      = assay s (0 + 1) ((t + 1 + 1) :: unfurl (t + 1) q₀ []) := by
                    have hsh' : coil (W s (t + 1)) t (W s (t + 1) n)
                        = assay s (0 + 1) (crank (t + 1) n) := hsh
                    rw [hsh', hcn0]
                  rw [hchsh]
                  have h3 := unstack
                    (assay s (0 + 1) ((t + 1 + 1) :: unfurl (t + 1) q₀ []) + 1)
                    (s (0 + rungs (t + 1) q₀ + (t + 1 + 1) + 2)) 2 hpu''
                  rw [h3]
                  show s (0 + rungs (t + 1) q₀ + (t + 1 + 1) + 2)
                    = s (rungs (t + 1) q₀ + t + 4)
                  rw [Nat.zero_add (rungs (t + 1) q₀)]
                  rfl
                have hcrch : crank (t + 1)
                    (coil (W s (t + 1)) t (W s (t + 1) n) + 1)
                    = [rungs (t + 1) q₀ + 2] := by
                  have h := the_crank_at_a_stair_number_is_one_stride (t + 1)
                    (rungs (t + 1) q₀ + 2) s hg hf
                  have hidx2 : t + 1 + (rungs (t + 1) q₀ + 2) + 1
                      = rungs (t + 1) q₀ + t + 4 := by
                    show t + 1 + rungs (t + 1) q₀ + 3 = rungs (t + 1) q₀ + t + 4
                    rw [seat_shuffles t (rungs (t + 1) q₀),
                      Nat.add_comm t (rungs (t + 1) q₀)]
                  rw [hidx2] at h
                  rw [hchain]
                  exact h
                have hcch : crank (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))
                    = 1 :: unfurl (t + 1) q₀ [] := by
                  rw [the_crank_steps_back (t + 1)
                    (coil (W s (t + 1)) t (W s (t + 1) n)), hcrch]
                  show (brand (t + 1) (rungs (t + 1) q₀ + 1)).2
                      :: unfurl (t + 1) (brand (t + 1) (rungs (t + 1) q₀ + 1)).1 [] = _
                  rw [the_brand_climbs_the_rungs (t + 1) q₀ 1
                    (Nat.succ_le_succ (Nat.zero_le t))]
                have hWch : W s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n)) + 1
                    = s (t + rungs (t + 1) q₀ + 3) := by
                  have hpu2 : assay s (t + 1) (1 :: unfurl (t + 1) q₀ []) + s (t + 3)
                      = s (t + rungs (t + 1) q₀ + 1 + 2) + s (t + 2) :=
                    a_purse_and_a_stair_make_a_beacon (t + 1) s hg q₀ 1 t
                  rw [the_first_flight_reads_two t s hg hf,
                    the_rail_reads_one t s hf] at hpu2
                  have hW : W s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))
                      = assay s (t + 1) (1 :: unfurl (t + 1) q₀ []) := by
                    show assay s (t + 1)
                      (crank (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))) = _
                    rw [hcch]
                  rw [hW]
                  exact Nat.succ.inj hpu2
                have hbridech : bride s (t + 1)
                    (coil (W s (t + 1)) t (W s (t + 1) n))
                    = s (t + rungs (t + 1) q₀ + 3) := by
                  show W s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))
                      + cond (veil (t + 1) (crank (t + 1)
                        (coil (W s (t + 1)) t (W s (t + 1) n) + 1))) 1 0
                    = s (t + rungs (t + 1) q₀ + 3)
                  rw [hcrch]
                  have hveilch : veil (t + 1) [rungs (t + 1) q₀ + 2] = true := by
                    show Nat.beq (brand (t + 1) (rungs (t + 1) q₀ + 1)).2 1 = true
                    rw [the_brand_climbs_the_rungs (t + 1) q₀ 1
                      (Nat.succ_le_succ (Nat.zero_le t))]
                    rfl
                  rw [hveilch]
                  exact hWch
                have hWn1 : W s (t + 1) (n + 1)
                    = s (t + rungs (t + 1) (q₀ + 1) + 2) := by
                  have hpu2 : assay s (t + 1) (0 :: unfurl (t + 1) (q₀ + 1) [])
                        + s (t + 2)
                      = s (t + rungs (t + 1) (q₀ + 1) + 0 + 2) + s (t + 1) :=
                    a_purse_and_a_stair_make_a_beacon (t + 1) s hg (q₀ + 1) 0 t
                  rw [the_rail_reads_one t s hf, the_floor_reads_one t s hf] at hpu2
                  have hW : W s (t + 1) (n + 1)
                      = assay s (t + 1) (0 :: unfurl (t + 1) (q₀ + 1) []) := by
                    show assay s (t + 1) (crank (t + 1) (n + 1)) = _
                    rw [hcn1, hq]
                  rw [hW]
                  have h' := unstack
                    (assay s (t + 1) (0 :: unfurl (t + 1) (q₀ + 1) []))
                    (s (t + rungs (t + 1) (q₀ + 1) + 0 + 2)) 1 hpu2
                  rw [h']
                have hgro : groom s (t + 1) (n + 1) + 1 = W s (t + 1) (n + 1) := by
                  show (W s (t + 1) (n + 1)
                      - cond (sash (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0) + 1
                    = W s (t + 1) (n + 1)
                  rw [hgn2]
                  exact sub_one_back (W s (t + 1) (n + 1))
                    (the_family_stays_awake t s hg hf n)
                have hn2 : n + 1 + 1 = s (t + rungs (t + 1) (q₀ + 1) + 3) := by
                  have hpu2 : assay s (t + 1 + 1) (0 :: unfurl (t + 1) (q₀ + 1) [])
                        + s (t + 1 + 0 + 2)
                      = s (t + 1 + rungs (t + 1) (q₀ + 1) + 0 + 2)
                        + s (t + 1 + 0 + 1) :=
                    a_purse_and_a_stair_make_a_beacon (t + 1) s hg (q₀ + 1) 0 (t + 1)
                  have hpu3 : assay s (t + 1 + 1) (0 :: unfurl (t + 1) (q₀ + 1) [])
                        + s (t + 3)
                      = s (t + 1 + rungs (t + 1) (q₀ + 1) + 0 + 2) + s (t + 2) := hpu2
                  rw [the_first_flight_reads_two t s hg hf,
                    the_rail_reads_one t s hf] at hpu3
                  have hdn : assay s (t + 1 + 1) (0 :: unfurl (t + 1) (q₀ + 1) [])
                      = n + 1 := by
                    have hd := the_dial_reads_true (t + 1) s hg hf (n + 1)
                    rw [hcn1, hq] at hd
                    exact hd
                  rw [hdn] at hpu3
                  have h3 : (n + 1 + 1) + 1
                      = s (t + 1 + rungs (t + 1) (q₀ + 1) + 0 + 2) + 1 := hpu3
                  have h4 := Nat.succ.inj h3
                  rw [h4]
                  show s (t + 1 + rungs (t + 1) (q₀ + 1) + 2)
                    = s (t + rungs (t + 1) (q₀ + 1) + 3)
                  rw [seat_shuffles t (rungs (t + 1) (q₀ + 1))]
                have hsum : (groom s (t + 1) (n + 1)
                      + bride s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))) + 1
                    = n + 1 + 1 := by
                  rw [add_swap_right (groom s (t + 1) (n + 1))
                    (bride s (t + 1) (coil (W s (t + 1)) t (W s (t + 1) n))) 1,
                    hgro, hbridech, hWn1, hn2]
                  have hgnm : s (t + rungs (t + 1) (q₀ + 1) + 3)
                      = s (t + rungs (t + 1) (q₀ + 1) + 2)
                        + s (rungs (t + 1) (q₀ + 1) + 1) :=
                    gnomon_tn t s hg (rungs (t + 1) (q₀ + 1))
                  rw [hgnm]
                  show s (t + rungs (t + 1) (q₀ + 1) + 2) + s (t + rungs (t + 1) q₀ + 3)
                    = s (t + rungs (t + 1) (q₀ + 1) + 2)
                      + s (rungs (t + 1) (q₀ + 1) + 1)
                  have hlast : t + rungs (t + 1) q₀ + 3
                      = rungs (t + 1) (q₀ + 1) + 1 := by
                    show t + rungs (t + 1) q₀ + 3 = rungs (t + 1) q₀ + (t + 1 + 1) + 1
                    rw [Nat.add_comm t (rungs (t + 1) q₀)]
                    rfl
                  rw [hlast]
                exact Nat.succ.inj hsum

/-- info: 'Foam.Bridges.the_family_marriage_closes_for_the_groom' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_marriage_closes_for_the_groom

theorem the_family_household_closes (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    bride s (t + 1) (n + 1)
        + coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)) = n + 1
      ∧ groom s (t + 1) (n + 1)
        + bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)) = n + 1 :=
  ⟨the_family_marriage_closes_for_the_bride t s hg hf hz n,
    the_family_marriage_closes_for_the_groom t s hg hf hz n⟩

theorem the_grounded_bride_satisfies_the_family_marriage (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    bride s (t + 1) (n + 1)
      = (n + 1) - coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)) :=
  calc bride s (t + 1) (n + 1)
      = (bride s (t + 1) (n + 1)
          + coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)))
        - coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)) :=
        (add_then_sub (bride s (t + 1) (n + 1))
          (coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)))).symm
    _ = (n + 1) - coil (W s (t + 1)) t (groom s (t + 1) (bride s (t + 1) n)) := by
        rw [the_family_marriage_closes_for_the_bride t s hg hf hz n]

theorem the_grounded_groom_satisfies_the_family_marriage (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hz : s 0 = 0) (n : Nat) :
    groom s (t + 1) (n + 1)
      = (n + 1) - bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)) :=
  calc groom s (t + 1) (n + 1)
      = (groom s (t + 1) (n + 1)
          + bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)))
        - bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)) :=
        (add_then_sub (groom s (t + 1) (n + 1))
          (bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)))).symm
    _ = (n + 1) - bride s (t + 1) (coil (W s (t + 1)) t (groom s (t + 1) n)) := by
        rw [the_family_marriage_closes_for_the_groom t s hg hf hz n]

/-- info: 'Foam.Bridges.the_family_household_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_household_closes

/-- info: 'Foam.Bridges.the_grounded_bride_satisfies_the_family_marriage' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_bride_satisfies_the_family_marriage

/-- info: 'Foam.Bridges.the_grounded_groom_satisfies_the_family_marriage' does not depend on any axioms -/
#guard_msgs in #print axioms the_grounded_groom_satisfies_the_family_marriage

theorem the_spelling_lights_the_beacon : ∀ (k : Nat), spell [k] = beacon k
  | 0 => rfl
  | k + 1 => congrArg (List.cons false) (the_spelling_lights_the_beacon k)

theorem the_rungs_pair_at_the_golden_register : ∀ (j : Nat), rungs 1 j = j + j
  | 0 => rfl
  | j + 1 => by
      show rungs 1 j + 2 = (j + 1) + (j + 1)
      rw [the_rungs_pair_at_the_golden_register j, seats_pair j]

/-- info: 'Foam.Bridges.the_spelling_lights_the_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms the_spelling_lights_the_beacon

/-- info: 'Foam.Bridges.the_rungs_pair_at_the_golden_register' does not depend on any axioms -/
#guard_msgs in #print axioms the_rungs_pair_at_the_golden_register

theorem the_veil_skips_two_strides (e g g' : Nat) (rest : List Nat) :
    veil e (g :: g' :: rest) = false := by
  cases g with
  | zero => rfl
  | succ p => rfl

theorem the_sash_skips_two_strides (e g g' : Nat) (rest : List Nat) :
    sash e (g :: g' :: rest) = false := by
  cases g with
  | zero => rfl
  | succ p => rfl

/-- info: 'Foam.Bridges.the_veil_skips_two_strides' does not depend on any axioms -/
#guard_msgs in #print axioms the_veil_skips_two_strides

/-- info: 'Foam.Bridges.the_sash_skips_two_strides' does not depend on any axioms -/
#guard_msgs in #print axioms the_sash_skips_two_strides

theorem the_veil_is_the_even_flag : ∀ (gs : List Nat), veil 1 gs = evenBeacon (spell gs)
  | [] => rfl
  | [0] => rfl
  | [p + 1] => by
      show Nat.beq (brand 1 p).2 1 = evenBeacon (spell [p + 1])
      rw [the_spelling_lights_the_beacon (p + 1)]
      cases every_seat_takes_a_side p with
      | inl hj =>
          match hj with
          | ⟨j, hjj⟩ =>
            subst hjj
            have hbr : brand 1 (rungs 1 j + 0) = (j, 0) :=
              the_brand_climbs_the_rungs 1 j 0 (Nat.zero_le 1)
            have hbr' : brand 1 (j + j) = (j, 0) := by
              rw [← the_rungs_pair_at_the_golden_register j]
              exact hbr
            rw [hbr', the_even_flag_skips_odd_beacons j]
            rfl
      | inr hj =>
          match hj with
          | ⟨j, hjj⟩ =>
            subst hjj
            have hbr : brand 1 (rungs 1 j + 1) = (j, 1) :=
              the_brand_climbs_the_rungs 1 j 1 (Nat.le_refl 1)
            have hbr' : brand 1 (j + j + 1) = (j, 1) := by
              rw [← the_rungs_pair_at_the_golden_register j]
              exact hbr
            rw [hbr']
            have hfly := the_even_flag_flies_on_its_beacon (j + 1)
            rw [seats_pair j] at hfly
            rw [hfly]
            rfl
  | g :: g' :: rest => by
      cases hE : evenBeacon (spell (g :: g' :: rest)) with
      | false => exact the_veil_skips_two_strides 1 g g' rest
      | true =>
          match the_even_flag_finds_its_beacon (spell (g :: g' :: rest)) hE with
          | ⟨j, hbe⟩ =>
            have hsp : spell (g :: g' :: rest) = spell [j + j] := by
              rw [hbe, the_spelling_lights_the_beacon (j + j)]
            have hun := congrArg unspell hsp
            rw [the_spelling_reads_back (g :: g' :: rest),
              the_spelling_reads_back [j + j]] at hun
            exact nomatch hun

theorem the_sash_is_the_odd_flag : ∀ (gs : List Nat), sash 1 gs = oddBeacon (spell gs)
  | [] => rfl
  | [0] => rfl
  | [p + 1] => by
      show Nat.beq (brand 1 p).2 0 = oddBeacon (spell [p + 1])
      rw [the_spelling_lights_the_beacon (p + 1)]
      cases every_seat_takes_a_side p with
      | inl hj =>
          match hj with
          | ⟨j, hjj⟩ =>
            subst hjj
            have hbr : brand 1 (rungs 1 j + 0) = (j, 0) :=
              the_brand_climbs_the_rungs 1 j 0 (Nat.zero_le 1)
            have hbr' : brand 1 (j + j) = (j, 0) := by
              rw [← the_rungs_pair_at_the_golden_register j]
              exact hbr
            rw [hbr', the_odd_flag_flies_on_its_beacon j]
            rfl
      | inr hj =>
          match hj with
          | ⟨j, hjj⟩ =>
            subst hjj
            have hbr : brand 1 (rungs 1 j + 1) = (j, 1) :=
              the_brand_climbs_the_rungs 1 j 1 (Nat.le_refl 1)
            have hbr' : brand 1 (j + j + 1) = (j, 1) := by
              rw [← the_rungs_pair_at_the_golden_register j]
              exact hbr
            rw [hbr']
            have hskip := the_odd_flag_skips_even_beacons (j + 1)
            rw [seats_pair j] at hskip
            rw [hskip]
            rfl
  | g :: g' :: rest => by
      cases hO : oddBeacon (spell (g :: g' :: rest)) with
      | false => exact the_sash_skips_two_strides 1 g g' rest
      | true =>
          match the_odd_flag_finds_its_beacon (spell (g :: g' :: rest)) hO with
          | ⟨j, hbe⟩ =>
            have hsp : spell (g :: g' :: rest) = spell [j + j + 1] := by
              rw [hbe, the_spelling_lights_the_beacon (j + j + 1)]
            have hun := congrArg unspell hsp
            rw [the_spelling_reads_back (g :: g' :: rest),
              the_spelling_reads_back [j + j + 1]] at hun
            exact nomatch hun

/-- info: 'Foam.Bridges.the_veil_is_the_even_flag' does not depend on any axioms -/
#guard_msgs in #print axioms the_veil_is_the_even_flag

/-- info: 'Foam.Bridges.the_sash_is_the_odd_flag' does not depend on any axioms -/
#guard_msgs in #print axioms the_sash_is_the_odd_flag

theorem the_family_reseals_the_bride (n : Nat) : bride fibN 1 n = F n := by
  show W fibN 1 n + cond (veil 1 (crank 1 (n + 1))) 1 0
    = G n + cond (evenBeacon (odometer (n + 1))) 1 0
  rw [the_walker_is_the_golden_cousin n, the_veil_is_the_even_flag (crank 1 (n + 1)),
    the_golden_crank_writes_the_golden_page (n + 1)]

theorem the_family_reseals_the_groom (n : Nat) : groom fibN 1 n = M n := by
  show W fibN 1 n - cond (sash 1 (crank 1 (n + 1))) 1 0
    = G n - cond (oddBeacon (odometer (n + 1))) 1 0
  rw [the_walker_is_the_golden_cousin n, the_sash_is_the_odd_flag (crank 1 (n + 1)),
    the_golden_crank_writes_the_golden_page (n + 1)]

theorem the_family_reseals_the_marriage (n : Nat) :
    F (n + 1) + M (F n) = n + 1 := by
  have h := the_family_marriage_closes_for_the_bride 0 fibN
    the_golden_staircase_holds_the_gnomon the_golden_staircase_holds_the_floor rfl n
  rw [the_family_reseals_the_bride (n + 1), the_family_reseals_the_bride n] at h
  show F (n + 1) + M (F n) = n + 1
  rw [← the_family_reseals_the_groom (F n)]
  exact h

/-- info: 'Foam.Bridges.the_family_reseals_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_bride

/-- info: 'Foam.Bridges.the_family_reseals_the_groom' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_groom

/-- info: 'Foam.Bridges.the_family_reseals_the_marriage' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_reseals_the_marriage

theorem the_herd_marriage_closes (n : Nat) :
    bride herdN 2 (n + 1) + W herdN 2 (groom herdN 2 (bride herdN 2 n)) = n + 1
      ∧ groom herdN 2 (n + 1) + bride herdN 2 (W herdN 2 (groom herdN 2 n)) = n + 1 :=
  ⟨the_family_marriage_closes_for_the_bride 1 herdN
      the_herd_holds_the_gnomon the_herd_holds_the_floor rfl n,
    the_family_marriage_closes_for_the_groom 1 herdN
      the_herd_holds_the_gnomon the_herd_holds_the_floor rfl n⟩

theorem the_herd_household_hums :
    (bride herdN 2 0, bride herdN 2 1, bride herdN 2 2, bride herdN 2 3,
      bride herdN 2 4, bride herdN 2 5, bride herdN 2 6, bride herdN 2 7,
      bride herdN 2 8, bride herdN 2 9, bride herdN 2 10, bride herdN 2 11)
      = (1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 7)
    ∧ (groom herdN 2 0, groom herdN 2 1, groom herdN 2 2, groom herdN 2 3,
      groom herdN 2 4, groom herdN 2 5, groom herdN 2 6, groom herdN 2 7,
      groom herdN 2 8, groom herdN 2 9, groom herdN 2 10, groom herdN 2 11)
      = (0, 0, 1, 2, 3, 3, 4, 5, 5, 6, 7, 7) := ⟨rfl, rfl⟩

theorem the_next_household_hums :
    (bride (stair 3) 3 0, bride (stair 3) 3 1, bride (stair 3) 3 2, bride (stair 3) 3 3,
      bride (stair 3) 3 4, bride (stair 3) 3 5, bride (stair 3) 3 6, bride (stair 3) 3 7,
      bride (stair 3) 3 8, bride (stair 3) 3 9, bride (stair 3) 3 10, bride (stair 3) 3 11)
      = (1, 1, 2, 2, 3, 4, 5, 5, 6, 7, 7, 8)
    ∧ (groom (stair 3) 3 0, groom (stair 3) 3 1, groom (stair 3) 3 2, groom (stair 3) 3 3,
      groom (stair 3) 3 4, groom (stair 3) 3 5, groom (stair 3) 3 6, groom (stair 3) 3 7,
      groom (stair 3) 3 8, groom (stair 3) 3 9, groom (stair 3) 3 10, groom (stair 3) 3 11)
      = (0, 0, 1, 2, 3, 4, 4, 5, 6, 6, 7, 8) := ⟨rfl, rfl⟩

theorem the_next_household_closes (n : Nat) :
    bride (stair 3) 3 (n + 1)
        + coil (W (stair 3) 3) 2 (groom (stair 3) 3 (bride (stair 3) 3 n)) = n + 1
      ∧ groom (stair 3) 3 (n + 1)
        + bride (stair 3) 3 (coil (W (stair 3) 3) 2 (groom (stair 3) 3 n)) = n + 1 :=
  ⟨the_family_marriage_closes_for_the_bride 2 (stair 3)
      (the_stairway_holds_the_gnomon 3) (the_stairway_holds_the_floor 3) rfl n,
    the_family_marriage_closes_for_the_groom 2 (stair 3)
      (the_stairway_holds_the_gnomon 3) (the_stairway_holds_the_floor 3) rfl n⟩

/-- info: 'Foam.Bridges.the_herd_marriage_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_marriage_closes

/-- info: 'Foam.Bridges.the_herd_household_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_household_hums

/-- info: 'Foam.Bridges.the_next_household_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_household_hums

/-- info: 'Foam.Bridges.the_next_household_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_household_closes

def crest (e r : Nat) : List Nat → Bool
  | [] => false
  | [0] => true
  | [p + 1] => Nat.beq (brand e p).2 r
  | _ :: _ :: _ => false

def spur (e r : Nat) : List Nat → Bool
  | [] => false
  | [0] => false
  | [p + 1] => Nat.beq (brand e p).2 r
  | _ :: _ :: _ => false

def matron (s : Nat → Nat) (e j n : Nat) : Nat :=
  coil (W s e) j n + cond (crest e j (crank e (n + 1))) 1 0

def patron (s : Nat → Nat) (e j n : Nat) : Nat :=
  coil (W s e) j n - cond (spur e (j - 1) (crank e (n + 1))) 1 0

theorem the_crest_is_the_veil (e : Nat) : ∀ (gs : List Nat), crest e 1 gs = veil e gs
  | [] => rfl
  | 0 :: [] => rfl
  | (_ + 1) :: [] => rfl
  | _ :: _ :: _ => rfl

theorem the_spur_is_the_sash (e : Nat) : ∀ (gs : List Nat), spur e 0 gs = sash e gs
  | [] => rfl
  | 0 :: [] => rfl
  | (_ + 1) :: [] => rfl
  | _ :: _ :: _ => rfl

theorem the_matron_is_the_bride (s : Nat → Nat) (e n : Nat) :
    matron s e 1 n = bride s e n := by
  show W s e n + cond (crest e 1 (crank e (n + 1))) 1 0
    = W s e n + cond (veil e (crank e (n + 1))) 1 0
  rw [the_crest_is_the_veil e (crank e (n + 1))]

theorem the_patron_is_the_groom (s : Nat → Nat) (e n : Nat) :
    patron s e 1 n = groom s e n := by
  show W s e n - cond (spur e 0 (crank e (n + 1))) 1 0
    = W s e n - cond (sash e (crank e (n + 1))) 1 0
  rw [the_spur_is_the_sash e (crank e (n + 1))]

/-- info: 'Foam.Bridges.the_crest_is_the_veil' does not depend on any axioms -/
#guard_msgs in #print axioms the_crest_is_the_veil

/-- info: 'Foam.Bridges.the_spur_is_the_sash' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_is_the_sash

/-- info: 'Foam.Bridges.the_matron_is_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms the_matron_is_the_bride

/-- info: 'Foam.Bridges.the_patron_is_the_groom' does not depend on any axioms -/
#guard_msgs in #print axioms the_patron_is_the_groom

theorem the_matron_wakes_lit (t j : Nat) (s : Nat → Nat) : matron s (t + 1) j 0 = 1 := by
  show coil (W s (t + 1)) j 0 + cond (crest (t + 1) j (crank (t + 1) 1)) 1 0 = 1
  rw [the_coil_rests_at_zero t s j]
  rfl

theorem the_patron_wakes_dark (t j : Nat) (s : Nat → Nat) : patron s (t + 1) j 0 = 0 := by
  show coil (W s (t + 1)) j 0 - cond (spur (t + 1) (j - 1) (crank (t + 1) 1)) 1 0 = 0
  rw [the_coil_rests_at_zero t s j]
  rfl

theorem the_elders_hold_the_deep_shadow (t j n : Nat) (s : Nat → Nat) :
    patron s (t + 1) j n ≤ coil (W s (t + 1)) j n
      ∧ coil (W s (t + 1)) j n ≤ matron s (t + 1) j n :=
  ⟨the_toll_never_gains (coil (W s (t + 1)) j n)
      (cond (spur (t + 1) (j - 1) (crank (t + 1) (n + 1))) 1 0),
    Nat.le_add_right (coil (W s (t + 1)) j n)
      (cond (crest (t + 1) j (crank (t + 1) (n + 1))) 1 0)⟩

theorem the_crest_and_spur_never_meet (e r : Nat) (gs : List Nat)
    (h : crest e (r + 1) gs = true) : spur e r gs = false := by
  match gs, h with
  | 0 :: [], _ => rfl
  | (p + 1) :: [], h =>
      have h2 : (brand e p).2 = r + 1 := Nat.eq_of_beq_eq_true h
      show Nat.beq (brand e p).2 r = false
      rw [h2]
      exact beq_shuts_high r (r + 1) (Nat.le_refl (r + 1))

/-- info: 'Foam.Bridges.the_matron_wakes_lit' does not depend on any axioms -/
#guard_msgs in #print axioms the_matron_wakes_lit

/-- info: 'Foam.Bridges.the_patron_wakes_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_patron_wakes_dark

/-- info: 'Foam.Bridges.the_elders_hold_the_deep_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms the_elders_hold_the_deep_shadow

/-- info: 'Foam.Bridges.the_crest_and_spur_never_meet' does not depend on any axioms -/
#guard_msgs in #print axioms the_crest_and_spur_never_meet

theorem the_herd_inlaws_hum :
    ((matron herdN 2 2 0, matron herdN 2 2 1, matron herdN 2 2 2, matron herdN 2 2 3,
        matron herdN 2 2 4, matron herdN 2 2 5, matron herdN 2 2 6, matron herdN 2 2 7,
        matron herdN 2 2 8, matron herdN 2 2 9, matron herdN 2 2 10, matron herdN 2 2 11),
      (patron herdN 2 2 0, patron herdN 2 2 1, patron herdN 2 2 2, patron herdN 2 2 3,
        patron herdN 2 2 4, patron herdN 2 2 5, patron herdN 2 2 6, patron herdN 2 2 7,
        patron herdN 2 2 8, patron herdN 2 2 9, patron herdN 2 2 10, patron herdN 2 2 11))
    = ((1, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5, 5),
      (0, 1, 0, 1, 2, 3, 3, 4, 3, 4, 5, 5)) := rfl

theorem the_upper_marriage_does_not_close :
    matron herdN 2 2 2 + patron herdN 2 2 (matron herdN 2 2 1) ≠ W herdN 2 2 :=
  fun h => nomatch Nat.succ.inj h

/-- info: 'Foam.Bridges.the_herd_inlaws_hum' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_inlaws_hum

/-- info: 'Foam.Bridges.the_upper_marriage_does_not_close' does not depend on any axioms -/
#guard_msgs in #print axioms the_upper_marriage_does_not_close

theorem a_branded_crossing_steps_the_walk (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n p r : Nat) (hpage : crank (t + 1) (n + 1) = [p + 1])
    (hbr : (brand (t + 1) p).2 = r + 1) (hre : r + 1 ≤ t + 1) :
    W s (t + 1) n + 1 = W s (t + 1) (n + 1) := by
  have hn1 : n + 1 = s (t + (p + 1) + 2) := a_crossing_reads_its_stair t s hg hf n (p + 1) hpage
  have hW1 : W s (t + 1) (n + 1) = s (t + p + 2) := by
    rw [hn1]
    exact the_family_beacon_slides t (p + 1) s hg hf
  have hcn : crank (t + 1) n = (r + 1) :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
    rw [the_crank_steps_back (t + 1) n, hpage, the_untick_opens_the_purse (t + 1) p, hbr]
  have hrungs : rungs (t + 1) (brand (t + 1) p).1 + (r + 1) = p := by
    have h := the_brand_reads_the_rungs (t + 1) p
    rw [hbr] at h
    exact h
  have hpu := a_purse_and_a_stair_make_a_beacon (t + 1) s hg (brand (t + 1) p).1 (r + 1) t
  have hidx : s (t + rungs (t + 1) (brand (t + 1) p).1 + (r + 1) + 2) = s (t + p + 2) := by
    have h : t + rungs (t + 1) (brand (t + 1) p).1 + (r + 1) + 2 = t + p + 2 := by
      rw [Nat.add_assoc t (rungs (t + 1) (brand (t + 1) p).1) (r + 1), hrungs]
    rw [h]
  rw [hidx] at hpu
  have hgn : s (t + (r + 1) + 2) = s (t + (r + 1) + 1) + 1 := by
    have h : s (t + r + 3) = s (t + r + 2) + s (r + 1) := gnomon_tn t s hg r
    rw [hf r (Nat.le_of_succ_le hre)] at h
    exact h
  rw [hgn] at hpu
  have hpu2 : assay s (t + 1) ((r + 1) :: unfurl (t + 1) (brand (t + 1) p).1 []) + 1
      + s (t + (r + 1) + 1)
      = s (t + p + 2) + s (t + (r + 1) + 1) := by
    rw [seat_shuffles (assay s (t + 1) ((r + 1) :: unfurl (t + 1) (brand (t + 1) p).1 []))
      (s (t + (r + 1) + 1))]
    exact hpu
  have hfin := unstack (assay s (t + 1) ((r + 1) :: unfurl (t + 1) (brand (t + 1) p).1 []) + 1)
    (s (t + p + 2)) (s (t + (r + 1) + 1)) hpu2
  rw [hW1]
  show assay s (t + 1) (crank (t + 1) n) + 1 = s (t + p + 2)
  rw [hcn]
  exact hfin

/-- info: 'Foam.Bridges.a_branded_crossing_steps_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms a_branded_crossing_steps_the_walk

theorem a_wrapped_crossing_rests_the_walk (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n p : Nat) (hpage : crank (t + 1) (n + 1) = [p + 1])
    (hbr : (brand (t + 1) p).2 = 0) :
    W s (t + 1) n = W s (t + 1) (n + 1) := by
  have hn1 : n + 1 = s (t + (p + 1) + 2) := a_crossing_reads_its_stair t s hg hf n (p + 1) hpage
  have hW1 : W s (t + 1) (n + 1) = s (t + p + 2) := by
    rw [hn1]
    exact the_family_beacon_slides t (p + 1) s hg hf
  have hcn : crank (t + 1) n = 0 :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
    rw [the_crank_steps_back (t + 1) n, hpage, the_untick_opens_the_purse (t + 1) p, hbr]
  have hrungs : rungs (t + 1) (brand (t + 1) p).1 = p := by
    have h := the_brand_reads_the_rungs (t + 1) p
    rw [hbr] at h
    exact h
  have hpu0 := a_purse_and_a_stair_make_a_beacon (t + 1) s hg (brand (t + 1) p).1 0 t
  have hpu : assay s (t + 1) (0 :: unfurl (t + 1) (brand (t + 1) p).1 []) + s (t + 2)
      = s (t + rungs (t + 1) (brand (t + 1) p).1 + 2) + s (t + 1) := hpu0
  rw [hrungs, hf (t + 1) (Nat.le_refl (t + 1)), hf t (Nat.le_succ t)] at hpu
  rw [hW1]
  show assay s (t + 1) (crank (t + 1) n) = s (t + p + 2)
  rw [hcn]
  exact Nat.succ.inj hpu

/-- info: 'Foam.Bridges.a_wrapped_crossing_rests_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms a_wrapped_crossing_rests_the_walk

theorem a_branded_crossing_pins_the_walked_page (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n p r : Nat)
    (hpage : crank (t + 1) (n + 1) = [p + 1]) (hbr : (brand (t + 1) p).2 = r + 1)
    (hre : r + 1 ≤ t + 1) :
    crank (t + 1) (W s (t + 1) n + 1) = [p] := by
  have hstep := a_branded_crossing_steps_the_walk t s hg hf n p r hpage hbr hre
  have hn1 : n + 1 = s (t + (p + 1) + 2) := a_crossing_reads_its_stair t s hg hf n (p + 1) hpage
  have hW1 : W s (t + 1) (n + 1) = s (t + p + 2) := by
    rw [hn1]
    exact the_family_beacon_slides t (p + 1) s hg hf
  rw [hstep, hW1]
  have h := the_crank_at_a_stair_number_is_one_stride (t + 1) p s hg hf
  have hix : t + 1 + p + 1 = t + p + 2 := congrArg (· + 1) (seat_shuffles t p)
  rw [hix] at h
  exact h

/-- info: 'Foam.Bridges.a_branded_crossing_pins_the_walked_page' does not depend on any axioms -/
#guard_msgs in #print axioms a_branded_crossing_pins_the_walked_page

theorem the_family_walks_forward (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (d a : Nat), W s (t + 1) a ≤ W s (t + 1) (a + d)
  | 0, a => Nat.le_refl (W s (t + 1) a)
  | d + 1, a => Nat.le_trans (the_family_walks_forward t s hg hf d a)
      (the_family_never_steps_back t s hg hf (a + d))

theorem the_hour_bounds_the_walk (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n v : Nat) (hW : W s (t + 1) n = v) :
    n ≤ stime s (t + 1) v := by
  cases Nat.decLe n (stime s (t + 1) v) with
  | isTrue h => exact h
  | isFalse h =>
      have hlt : stime s (t + 1) v + 1 ≤ n := Nat.gt_of_not_le h
      match Nat.le.dest hlt with
      | ⟨d, hd⟩ =>
          have hmono := the_family_walks_forward t s hg hf d (stime s (t + 1) v + 1)
          rw [hd, the_family_walks_at_the_first_beat t s hg hf v, hW] at hmono
          exact absurd hmono (Nat.not_succ_le_self v)

theorem the_walk_needs_its_hour (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n v : Nat) (hW : W s (t + 1) n = v + 1) :
    stime s (t + 1) v + 1 ≤ n := by
  cases Nat.decLe (stime s (t + 1) v + 1) n with
  | isTrue h => exact h
  | isFalse h =>
      have hle : n ≤ stime s (t + 1) v := Nat.le_of_succ_le_succ (Nat.gt_of_not_le h)
      match Nat.le.dest hle with
      | ⟨d, hd⟩ =>
          have hmono := the_family_walks_forward t s hg hf d n
          rw [hd, the_family_arrives_on_the_hour t s hg hf v, hW] at hmono
          exact absurd hmono (Nat.not_succ_le_self v)

/-- info: 'Foam.Bridges.the_family_walks_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_walks_forward

/-- info: 'Foam.Bridges.the_hour_bounds_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_hour_bounds_the_walk

/-- info: 'Foam.Bridges.the_walk_needs_its_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_needs_its_hour

theorem the_walk_pins_the_page_below (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n p r : Nat)
    (hpage : crank (t + 1) (W s (t + 1) n + 1) = [p + 1])
    (hbr : (brand (t + 1) p).2 = r + 1) (hre : r + 2 ≤ t + 1) :
    crank (t + 1) (n + 1) = [rungs (t + 1) (brand (t + 1) p).1 + r + 3] := by
  cases hWn : W s (t + 1) n with
  | zero =>
      rw [hWn] at hpage
      have hpage' : [0] = [p + 1] := hpage
      injection hpage' with h1 _
      exact nomatch h1
  | succ μ =>
      rw [hWn] at hpage
      have hp1 : crank (t + 1) (μ + 1)
          = (r + 1) :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
        rw [the_crank_steps_back (t + 1) (μ + 1), hpage,
          the_untick_opens_the_purse (t + 1) p, hbr]
      have hbr2 : brand (t + 1) r = (0, r) := by
        have h : brand (t + 1) (0 + r) = (0, r) :=
          the_brand_climbs_the_rungs (t + 1) 0 r
            (Nat.le_of_succ_le (Nat.le_of_succ_le hre))
        rw [Nat.zero_add r] at h
        exact h
      have hp0 : crank (t + 1) μ
          = r :: unfurl (t + 1) 0 (unfurl (t + 1) (brand (t + 1) p).1 []) := by
        rw [the_crank_steps_back (t + 1) μ, hp1]
        show (brand (t + 1) r).2
            :: unfurl (t + 1) (brand (t + 1) r).1 (unfurl (t + 1) (brand (t + 1) p).1 [])
          = r :: unfurl (t + 1) 0 (unfurl (t + 1) (brand (t + 1) p).1 [])
        rw [hbr2]
      have hroomy : roomy (t + 1) (crank (t + 1) μ) = false := by
        rw [hp0]
        show Nat.ble (t + 1) r = false
        exact ble_shuts_high r (t + 1) (Nat.le_of_succ_le hre)
      have hbeat : stime s (t + 1) (μ + 1) = stime s (t + 1) μ + 1 := by
        rw [the_family_beat_reads_the_gate t s hg hf μ, hroomy]
        rfl
      have hup : n ≤ stime s (t + 1) (μ + 1) :=
        the_hour_bounds_the_walk t s hg hf n (μ + 1) hWn
      have hdown : stime s (t + 1) (μ + 1) ≤ n := by
        rw [hbeat]
        exact the_walk_needs_its_hour t s hg hf n μ hWn
      have hn : n = stime s (t + 1) (μ + 1) := Nat.le_antisymm hup hdown
      have hcn : crank (t + 1) n = (r + 2) :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
        rw [hn, the_family_hour_writes_the_page_above t s hg hf (μ + 1), hp1]
        rfl
      show tick (t + 1) (crank (t + 1) n) = [rungs (t + 1) (brand (t + 1) p).1 + r + 3]
      rw [hcn]
      exact the_tick_tops_the_purse (t + 1) (r + 1) (brand (t + 1) p).1 hre

/-- info: 'Foam.Bridges.the_walk_pins_the_page_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_pins_the_page_below

theorem the_crest_skips_two_strides (e r g g' : Nat) (rest : List Nat) :
    crest e r (g :: g' :: rest) = false := by
  cases g with
  | zero => rfl
  | succ _ => rfl

theorem the_spur_skips_two_strides (e r g g' : Nat) (rest : List Nat) :
    spur e r (g :: g' :: rest) = false := by
  cases g with
  | zero => rfl
  | succ _ => rfl

/-- info: 'Foam.Bridges.the_crest_skips_two_strides' does not depend on any axioms -/
#guard_msgs in #print axioms the_crest_skips_two_strides

/-- info: 'Foam.Bridges.the_spur_skips_two_strides' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_skips_two_strides

theorem the_crest_slides_forward (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (m r : Nat) (hre : r + 2 ≤ t + 1)
    (hflag : crest (t + 1) (r + 2) (crank (t + 1) (m + 1 + 1)) = true) :
    crest (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) (m + 1) + 1)) = true := by
  cases hc : crank (t + 1) (m + 1 + 1) with
  | nil => rw [hc] at hflag; exact nomatch hflag
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
              rw [hc, the_crest_skips_two_strides (t + 1) (r + 2) g g₂ gs₂] at hflag
              exact nomatch hflag
      | nil =>
          cases g with
          | zero =>
              have hd := the_dial_reads_true (t + 1) s hg hf (m + 1 + 1)
              rw [hc] at hd
              have hd' : s (t + 2) = m + 1 + 1 := hd
              rw [hf (t + 1) (Nat.le_refl (t + 1))] at hd'
              exact nomatch (Nat.succ.inj hd')
          | succ p =>
              rw [hc] at hflag
              have hbr : (brand (t + 1) p).2 = r + 2 := Nat.eq_of_beq_eq_true hflag
              cases p with
              | zero => exact nomatch hbr
              | succ p₁ =>
                  have hpin := a_branded_crossing_pins_the_walked_page t s hg hf
                    (m + 1) (p₁ + 1) (r + 1) hc hbr hre
                  rw [hpin]
                  show Nat.beq (brand (t + 1) p₁).2 (r + 1) = true
                  rw [the_brand_steps_back (t + 1) p₁ (r + 1) hbr]
                  exact beq_mirrors (r + 1)

theorem the_walked_crest_reads_back (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (m r : Nat) (hre : r + 2 ≤ t + 1)
    (hflag : crest (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) (m + 1) + 1)) = true) :
    crest (t + 1) (r + 2) (crank (t + 1) (m + 1 + 1)) = true := by
  cases hc' : crank (t + 1) (W s (t + 1) (m + 1) + 1) with
  | nil => rw [hc'] at hflag; exact nomatch hflag
  | cons g' gs' =>
      cases gs' with
      | cons g₂ gs₂ =>
              rw [hc', the_crest_skips_two_strides (t + 1) (r + 1) g' g₂ gs₂] at hflag
              exact nomatch hflag
      | nil =>
          cases g' with
          | zero =>
              have hd := the_dial_reads_true (t + 1) s hg hf (W s (t + 1) (m + 1) + 1)
              rw [hc'] at hd
              have hd' : s (t + 2) = W s (t + 1) (m + 1) + 1 := hd
              rw [hf (t + 1) (Nat.le_refl (t + 1))] at hd'
              have hz : 0 = W s (t + 1) (m + 1) := Nat.succ.inj hd'
              have haw := the_family_stays_awake t s hg hf m
              rw [← hz] at haw
              exact absurd haw (Nat.not_succ_le_zero 0)
          | succ p' =>
              rw [hc'] at hflag
              have hbr' : (brand (t + 1) p').2 = r + 1 := Nat.eq_of_beq_eq_true hflag
              have hpin := the_walk_pins_the_page_below t s hg hf (m + 1) p' r hc' hbr' hre
              rw [hpin]
              show Nat.beq (brand (t + 1) (rungs (t + 1) (brand (t + 1) p').1 + r + 2)).2
                  (r + 2) = true
              have hcl : brand (t + 1) (rungs (t + 1) (brand (t + 1) p').1 + r + 2)
                  = ((brand (t + 1) p').1, r + 2) :=
                the_brand_climbs_the_rungs (t + 1) (brand (t + 1) p').1 (r + 2) hre
              rw [hcl]
              exact beq_mirrors (r + 2)

/-- info: 'Foam.Bridges.the_crest_slides_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_crest_slides_forward

/-- info: 'Foam.Bridges.the_walked_crest_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_walked_crest_reads_back

theorem the_crest_slides_down_the_walk (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (r n : Nat) (hre : r + 2 ≤ t + 1) :
    crest (t + 1) (r + 2) (crank (t + 1) (n + 1))
      = crest (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) n + 1)) := by
  cases n with
  | zero => rfl
  | succ m =>
      cases hL : crest (t + 1) (r + 2) (crank (t + 1) (m + 1 + 1)) with
      | true => rw [the_crest_slides_forward t s hg hf m r hre hL]
      | false =>
          cases hR : crest (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) (m + 1) + 1)) with
          | false => rfl
          | true =>
              rw [the_walked_crest_reads_back t s hg hf m r hre hR] at hL
              exact nomatch hL

/-- info: 'Foam.Bridges.the_crest_slides_down_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_crest_slides_down_the_walk

theorem the_spur_slides_forward (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n r : Nat) (hre : r + 2 ≤ t + 1)
    (hflag : spur (t + 1) (r + 2) (crank (t + 1) (n + 1)) = true) :
    spur (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) n + 1)) = true := by
  cases hc : crank (t + 1) (n + 1) with
  | nil => rw [hc] at hflag; exact nomatch hflag
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
              rw [hc, the_spur_skips_two_strides (t + 1) (r + 2) g g₂ gs₂] at hflag
              exact nomatch hflag
      | nil =>
          cases g with
          | zero => rw [hc] at hflag; exact nomatch hflag
          | succ p =>
              rw [hc] at hflag
              have hbr : (brand (t + 1) p).2 = r + 2 := Nat.eq_of_beq_eq_true hflag
              cases p with
              | zero => exact nomatch hbr
              | succ p₁ =>
                  have hpin := a_branded_crossing_pins_the_walked_page t s hg hf
                    n (p₁ + 1) (r + 1) hc hbr hre
                  rw [hpin]
                  show Nat.beq (brand (t + 1) p₁).2 (r + 1) = true
                  rw [the_brand_steps_back (t + 1) p₁ (r + 1) hbr]
                  exact beq_mirrors (r + 1)

theorem the_walked_spur_reads_back (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (m r : Nat) (hre : r + 2 ≤ t + 1)
    (hflag : spur (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) (m + 1) + 1)) = true) :
    spur (t + 1) (r + 2) (crank (t + 1) (m + 1 + 1)) = true := by
  cases hc' : crank (t + 1) (W s (t + 1) (m + 1) + 1) with
  | nil => rw [hc'] at hflag; exact nomatch hflag
  | cons g' gs' =>
      cases gs' with
      | cons g₂ gs₂ =>
              rw [hc', the_spur_skips_two_strides (t + 1) (r + 1) g' g₂ gs₂] at hflag
              exact nomatch hflag
      | nil =>
          cases g' with
          | zero => rw [hc'] at hflag; exact nomatch hflag
          | succ p' =>
              rw [hc'] at hflag
              have hbr' : (brand (t + 1) p').2 = r + 1 := Nat.eq_of_beq_eq_true hflag
              have hpin := the_walk_pins_the_page_below t s hg hf (m + 1) p' r hc' hbr' hre
              rw [hpin]
              show Nat.beq (brand (t + 1) (rungs (t + 1) (brand (t + 1) p').1 + r + 2)).2
                  (r + 2) = true
              have hcl : brand (t + 1) (rungs (t + 1) (brand (t + 1) p').1 + r + 2)
                  = ((brand (t + 1) p').1, r + 2) :=
                the_brand_climbs_the_rungs (t + 1) (brand (t + 1) p').1 (r + 2) hre
              rw [hcl]
              exact beq_mirrors (r + 2)

theorem the_spur_slides_down_the_walk (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (r n : Nat) (hre : r + 2 ≤ t + 1) :
    spur (t + 1) (r + 2) (crank (t + 1) (n + 1))
      = spur (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) n + 1)) := by
  cases n with
  | zero => rfl
  | succ m =>
      cases hL : spur (t + 1) (r + 2) (crank (t + 1) (m + 1 + 1)) with
      | true => rw [the_spur_slides_forward t s hg hf (m + 1) r hre hL]
      | false =>
          cases hR : spur (t + 1) (r + 1) (crank (t + 1) (W s (t + 1) (m + 1) + 1)) with
          | false => rfl
          | true =>
              rw [the_walked_spur_reads_back t s hg hf m r hre hR] at hL
              exact nomatch hL

/-- info: 'Foam.Bridges.the_spur_slides_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_slides_forward

/-- info: 'Foam.Bridges.the_walked_spur_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_walked_spur_reads_back

/-- info: 'Foam.Bridges.the_spur_slides_down_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_slides_down_the_walk

theorem the_matron_speaks_one_altitude_down (t j : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hj : j + 2 ≤ t + 1) (n : Nat) :
    matron s (t + 1) (j + 2) n = matron s (t + 1) (j + 1) (W s (t + 1) n) := by
  show coil (W s (t + 1)) (j + 2) n
      + cond (crest (t + 1) (j + 2) (crank (t + 1) (n + 1))) 1 0
    = coil (W s (t + 1)) (j + 1) (W s (t + 1) n)
      + cond (crest (t + 1) (j + 1) (crank (t + 1) (W s (t + 1) n + 1))) 1 0
  rw [the_crest_slides_down_the_walk t s hg hf j n hj]
  rfl

theorem the_patron_speaks_one_altitude_down (t j : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (hj : j + 3 ≤ t + 1) (n : Nat) :
    patron s (t + 1) (j + 3) n = patron s (t + 1) (j + 2) (W s (t + 1) n) := by
  show coil (W s (t + 1)) (j + 3) n
      - cond (spur (t + 1) (j + 2) (crank (t + 1) (n + 1))) 1 0
    = coil (W s (t + 1)) (j + 2) (W s (t + 1) n)
      - cond (spur (t + 1) (j + 1) (crank (t + 1) (W s (t + 1) n + 1))) 1 0
  rw [the_spur_slides_down_the_walk t s hg hf j n (Nat.le_of_succ_le hj)]
  rfl

/-- info: 'Foam.Bridges.the_matron_speaks_one_altitude_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_matron_speaks_one_altitude_down

/-- info: 'Foam.Bridges.the_patron_speaks_one_altitude_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_patron_speaks_one_altitude_down

theorem the_spur_slides_to_the_wrap (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat)
    (h1 : spur (t + 1) 1 (crank (t + 1) (n + 1)) = true) :
    spur (t + 1) 0 (crank (t + 1) (W s (t + 1) n + 1)) = true := by
  cases hc : crank (t + 1) (n + 1) with
  | nil => rw [hc] at h1; exact nomatch h1
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
          rw [hc, the_spur_skips_two_strides (t + 1) 1 g g₂ gs₂] at h1
          exact nomatch h1
      | nil =>
          cases g with
          | zero => rw [hc] at h1; exact nomatch h1
          | succ k =>
              rw [hc] at h1
              have hbr : (brand (t + 1) k).2 = 1 := Nat.eq_of_beq_eq_true h1
              cases k with
              | zero => exact nomatch hbr
              | succ k₁ =>
                  have hpin := a_branded_crossing_pins_the_walked_page t s hg hf
                    n (k₁ + 1) 0 hc hbr (Nat.succ_le_succ (Nat.zero_le t))
                  rw [hpin]
                  show Nat.beq (brand (t + 1) k₁).2 0 = true
                  rw [the_brand_steps_back (t + 1) k₁ 0 hbr]
                  rfl

/-- info: 'Foam.Bridges.the_spur_slides_to_the_wrap' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_slides_to_the_wrap

theorem the_low_wrap_holds_the_walk (t : Nat) (s : Nat → Nat)
    (hf : Floored (t + 1) s) : ∀ (gs : List Nat),
    assay s (t + 1) (0 :: unfurl (t + 1) 0 gs) = assay s (t + 1) (1 :: gs)
  | [] => by
      show s (t + 1) + (0 : Nat) = s (t + 2) + 0
      rw [hf t (Nat.le_succ t), hf (t + 1) (Nat.le_refl (t + 1))]
  | g :: rest => by
      show s (t + 1) + (s (t + 2 + g + 1) + assay s (t + 2 + g + 1 + 1) rest)
        = s (t + 2) + (s (t + 3 + g) + assay s (t + 3 + g + 1) rest)
      have hidx : t + 3 + g = t + 2 + g + 1 := seat_shuffles (t + 2) g
      rw [hidx, hf t (Nat.le_succ t), hf (t + 1) (Nat.le_refl (t + 1))]

/-- info: 'Foam.Bridges.the_low_wrap_holds_the_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_low_wrap_holds_the_walk

theorem the_veil_shades_the_wrap (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat)
    (hv : veil (t + 1) (crank (t + 1) (n + 2)) = true) :
    spur (t + 1) 0 (crank (t + 1) (W s (t + 1) n + 1)) = true := by
  cases hc : crank (t + 1) (n + 2) with
  | nil => rw [hc] at hv; exact nomatch hv
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
          rw [hc, the_veil_skips_two_strides (t + 1) g g₂ gs₂] at hv
          exact nomatch hv
      | nil =>
          cases g with
          | zero =>
              have hd := the_dial_reads_true (t + 1) s hg hf (n + 2)
              rw [hc] at hd
              have hd' : s (t + 2) = n + 2 := hd
              rw [hf (t + 1) (Nat.le_refl (t + 1))] at hd'
              exact nomatch (Nat.succ.inj hd')
          | succ k =>
              rw [hc] at hv
              have hbr : (brand (t + 1) k).2 = 1 := Nat.eq_of_beq_eq_true hv
              have hp1 : crank (t + 1) (n + 1)
                  = 1 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
                rw [the_crank_steps_back (t + 1) (n + 1), hc,
                  the_untick_opens_the_purse (t + 1) k, hbr]
              have hp0 : crank (t + 1) n
                  = 0 :: unfurl (t + 1) 0 (unfurl (t + 1) (brand (t + 1) k).1 []) := by
                rw [the_crank_steps_back (t + 1) n, hp1]
                rfl
              have hWflat : W s (t + 1) n = W s (t + 1) (n + 1) := by
                show assay s (t + 1) (crank (t + 1) n)
                  = assay s (t + 1) (crank (t + 1) (n + 1))
                rw [hp0, hp1]
                exact the_low_wrap_holds_the_walk t s hf
                  (unfurl (t + 1) (brand (t + 1) k).1 [])
              cases k with
              | zero => exact nomatch hbr
              | succ k₁ =>
                  have hpin := a_branded_crossing_pins_the_walked_page t s hg hf
                    (n + 1) (k₁ + 1) 0 hc hbr (Nat.succ_le_succ (Nat.zero_le t))
                  rw [hWflat, hpin]
                  show Nat.beq (brand (t + 1) k₁).2 0 = true
                  rw [the_brand_steps_back (t + 1) k₁ 0 hbr]
                  rfl

/-- info: 'Foam.Bridges.the_veil_shades_the_wrap' does not depend on any axioms -/
#guard_msgs in #print axioms the_veil_shades_the_wrap

theorem the_wrap_names_its_two_seats (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat)
    (hL : spur (t + 1) 0 (crank (t + 1) (W s (t + 1) n + 1)) = true) :
    (spur (t + 1) 1 (crank (t + 1) (n + 1)) || veil (t + 1) (crank (t + 1) (n + 2)))
      = true := by
  cases hc : crank (t + 1) (W s (t + 1) n + 1) with
  | nil => rw [hc] at hL; exact nomatch hL
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
          rw [hc, the_spur_skips_two_strides (t + 1) 0 g g₂ gs₂] at hL
          exact nomatch hL
      | nil =>
          cases g with
          | zero => rw [hc] at hL; exact nomatch hL
          | succ p =>
              rw [hc] at hL
              have hbr : (brand (t + 1) p).2 = 0 := Nat.eq_of_beq_eq_true hL
              have hrungs : rungs (t + 1) (brand (t + 1) p).1 = p := by
                have h := the_brand_reads_the_rungs (t + 1) p
                rw [hbr] at h
                exact h
              cases hq : (brand (t + 1) p).1 with
              | zero =>
                  rw [hq] at hrungs
                  have hp0 : (0 : Nat) = p := hrungs
                  subst hp0
                  have hd := the_dial_reads_true (t + 1) s hg hf (W s (t + 1) n + 1)
                  rw [hc] at hd
                  have hd' : s (t + 3) = W s (t + 1) n + 1 := hd
                  rw [the_first_flight_reads_two t s hg hf] at hd'
                  have hW1 : W s (t + 1) n = 1 := (Nat.succ.inj hd').symm
                  have hup : n ≤ stime s (t + 1) 1 :=
                    the_hour_bounds_the_walk t s hg hf n 1 hW1
                  have hdown : stime s (t + 1) 0 + 1 ≤ n :=
                    the_walk_needs_its_hour t s hg hf n 0 hW1
                  have hst1 : stime s (t + 1) 1 = 2 := by
                    rw [the_family_beat_reads_the_gate t s hg hf 0]
                    rfl
                  rw [hst1] at hup
                  have hd1 : (1 : Nat) ≤ n := hdown
                  cases n with
                  | zero => exact absurd hd1 (Nat.not_succ_le_zero 0)
                  | succ n₁ =>
                      have hc3 : crank (t + 1) 3 = [2] := by
                        show tick (t + 1) (crank (t + 1) 2) = [2]
                        have hc2 : crank (t + 1) 2 = [1] := rfl
                        rw [hc2]
                        exact the_tick_climbs_the_floor (t + 1) 1
                          (Nat.succ_le_succ (Nat.zero_le t))
                      cases n₁ with
                      | zero =>
                          rw [hc3]
                          show (spur (t + 1) 1 [1]
                              || Nat.beq (brand (t + 1) 1).2 1) = true
                          rw [(rfl : brand (t + 1) 1 = (0, 1))]
                          rfl
                      | succ n₂ =>
                          cases n₂ with
                          | zero =>
                              rw [hc3]
                              show (Nat.beq (brand (t + 1) 1).2 1
                                  || veil (t + 1) (crank (t + 1) 4)) = true
                              rw [(rfl : brand (t + 1) 1 = (0, 1))]
                              rfl
                          | succ n₃ =>
                              have h3 : n₃ + 3 ≤ 2 := hup
                              exact absurd (Nat.le_of_succ_le_succ
                                  (Nat.le_of_succ_le_succ h3))
                                (Nat.not_succ_le_zero n₃)
              | succ q₁ =>
                  cases hWn : W s (t + 1) n with
                  | zero =>
                      rw [hWn] at hc
                      have hc1 : [0] = [p + 1] := hc
                      injection hc1 with h0 _
                      exact nomatch h0
                  | succ μ =>
                      rw [hWn] at hc
                      have hp1 : crank (t + 1) (μ + 1)
                          = 0 :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
                        rw [the_crank_steps_back (t + 1) (μ + 1), hc,
                          the_untick_opens_the_purse (t + 1) p, hbr]
                      have hp0 : crank (t + 1) μ
                          = (t + 2) :: unfurl (t + 1) q₁ [] := by
                        rw [the_crank_steps_back (t + 1) μ, hp1, hq]
                        rfl
                      have hroomy : roomy (t + 1) (crank (t + 1) μ) = true := by
                        rw [hp0]
                        exact Nat.ble_eq_true_of_le (Nat.le_succ (t + 1))
                      have hbeat : stime s (t + 1) (μ + 1) = stime s (t + 1) μ + 2 := by
                        rw [the_family_beat_reads_the_gate t s hg hf μ, hroomy]
                        rfl
                      have hdown : stime s (t + 1) μ + 1 ≤ n :=
                        the_walk_needs_its_hour t s hg hf n μ hWn
                      have hup : n ≤ stime s (t + 1) μ + 2 := by
                        rw [← hbeat]
                        exact the_hour_bounds_the_walk t s hg hf n (μ + 1) hWn
                      match Nat.le.dest hdown with
                      | ⟨d, hd⟩ =>
                          have hd2 : stime s (t + 1) μ + 1 + d ≤ stime s (t + 1) μ + 2 := by
                            rw [hd]
                            exact hup
                          rw [seat_shuffles (stime s (t + 1) μ) d] at hd2
                          have hdle : d + 1 ≤ 2 :=
                            stack_free (stime s (t + 1) μ) (d + 1) 2 hd2
                          cases d with
                          | zero =>
                              have hn : stime s (t + 1) μ + 1 = n := hd
                              have hcn1 : crank (t + 1) (n + 1)
                                  = 1 :: unfurl (t + 1) (brand (t + 1) p).1 [] := by
                                rw [← hn]
                                show tick (t + 1) (tick (t + 1)
                                    (crank (t + 1) (stime s (t + 1) μ)))
                                  = 1 :: unfurl (t + 1) (brand (t + 1) p).1 []
                                rw [the_family_hour_writes_the_page_above t s hg hf μ]
                                rw [tick_twice_rides_the_lift t (crank (t + 1) μ) hroomy]
                                show lift 1 (crank (t + 1) (μ + 1))
                                  = 1 :: unfurl (t + 1) (brand (t + 1) p).1 []
                                rw [hp1]
                                rfl
                              have hcn2 : crank (t + 1) (n + 2)
                                  = [rungs (t + 1) (brand (t + 1) p).1 + 2] := by
                                show tick (t + 1) (crank (t + 1) (n + 1))
                                  = [rungs (t + 1) (brand (t + 1) p).1 + 2]
                                rw [hcn1]
                                exact the_tick_tops_the_purse (t + 1) 0
                                  (brand (t + 1) p).1 (Nat.succ_le_succ (Nat.zero_le t))
                              rw [hcn1, hcn2, hq]
                              show (spur (t + 1) 1 (1 :: (t + 1) :: unfurl (t + 1) q₁ [])
                                  || Nat.beq
                                    (brand (t + 1) (rungs (t + 1) (q₁ + 1) + 1)).2 1)
                                = true
                              rw [the_spur_skips_two_strides (t + 1) 1 1 (t + 1)
                                (unfurl (t + 1) q₁ [])]
                              have hcl : brand (t + 1) (rungs (t + 1) (q₁ + 1) + 1)
                                  = (q₁ + 1, 1) :=
                                the_brand_climbs_the_rungs (t + 1) (q₁ + 1) 1
                                  (Nat.succ_le_succ (Nat.zero_le t))
                              rw [hcl]
                              rfl
                          | succ d' =>
                              cases d' with
                              | zero =>
                                  have hn' : n = stime s (t + 1) (μ + 1) := by
                                    rw [hbeat]
                                    exact hd.symm
                                  have hcn1 : crank (t + 1) (n + 1)
                                      = [rungs (t + 1) (brand (t + 1) p).1 + 2] := by
                                    rw [hn']
                                    show tick (t + 1)
                                        (crank (t + 1) (stime s (t + 1) (μ + 1)))
                                      = [rungs (t + 1) (brand (t + 1) p).1 + 2]
                                    rw [the_family_hour_writes_the_page_above t s hg hf
                                      (μ + 1), hp1]
                                    show tick (t + 1)
                                        (1 :: unfurl (t + 1) (brand (t + 1) p).1 [])
                                      = [rungs (t + 1) (brand (t + 1) p).1 + 2]
                                    exact the_tick_tops_the_purse (t + 1) 0
                                      (brand (t + 1) p).1
                                      (Nat.succ_le_succ (Nat.zero_le t))
                                  rw [hcn1]
                                  show (Nat.beq (brand (t + 1)
                                        (rungs (t + 1) (brand (t + 1) p).1 + 1)).2 1
                                      || veil (t + 1) (crank (t + 1) (n + 2))) = true
                                  have hcl : brand (t + 1)
                                      (rungs (t + 1) (brand (t + 1) p).1 + 1)
                                      = ((brand (t + 1) p).1, 1) :=
                                    the_brand_climbs_the_rungs (t + 1)
                                      (brand (t + 1) p).1 1
                                      (Nat.succ_le_succ (Nat.zero_le t))
                                  rw [hcl]
                                  rfl
                              | succ d'' =>
                                  exact absurd (Nat.le_of_succ_le_succ
                                      (Nat.le_of_succ_le_succ hdle))
                                    (Nat.not_succ_le_zero d'')

/-- info: 'Foam.Bridges.the_wrap_names_its_two_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_wrap_names_its_two_seats

theorem the_spur_and_the_oncoming_veil_never_meet (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n : Nat)
    (h1 : spur (t + 1) 1 (crank (t + 1) (n + 1)) = true) :
    veil (t + 1) (crank (t + 1) (n + 2)) = false := by
  cases hc : crank (t + 1) (n + 1) with
  | nil => rw [hc] at h1; exact nomatch h1
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
          rw [hc, the_spur_skips_two_strides (t + 1) 1 g g₂ gs₂] at h1
          exact nomatch h1
      | nil =>
          cases g with
          | zero => rw [hc] at h1; exact nomatch h1
          | succ k =>
              rw [hc] at h1
              have hbr : (brand (t + 1) k).2 = 1 := Nat.eq_of_beq_eq_true h1
              have hnext : crank (t + 1) (n + 2) = tick (t + 1) [k + 1] := by
                show tick (t + 1) (crank (t + 1) (n + 1)) = tick (t + 1) [k + 1]
                rw [hc]
              cases Nat.decLe (k + 1) (t + 1) with
              | isTrue hle =>
                  rw [hnext, the_tick_climbs_the_floor (t + 1) (k + 1) hle]
                  show Nat.beq (brand (t + 1) (k + 1)).2 1 = false
                  cases t with
                  | zero =>
                      have hb : Nat.beq (brand 1 k).2 1 = true := by
                        rw [hbr]
                        rfl
                      rw [brand_wraps 1 k hb]
                      rfl
                  | succ t' =>
                      have hb : Nat.beq (brand (t' + 2) k).2 (t' + 2) = false := by
                        rw [hbr]
                        exact beq_shuts_low 1 (t' + 2)
                          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le t')))
                      rw [brand_steps (t' + 2) k hb, hbr]
                      rfl
              | isFalse hgt =>
                  have hlt : t + 2 ≤ k + 1 := Nat.gt_of_not_le hgt
                  match Nat.le.dest hlt with
                  | ⟨w, hw⟩ =>
                      have htk : tick (t + 1) [k + 1] = [0, t + 1 + w] := by
                        rw [← hw]
                        exact the_tick_leaves_the_rail (t + 1) w
                      rw [hnext, htk,
                        the_veil_skips_two_strides (t + 1) 0 (t + 1 + w) []]

/-- info: 'Foam.Bridges.the_spur_and_the_oncoming_veil_never_meet' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_and_the_oncoming_veil_never_meet

theorem the_spur_snags_on_the_veil (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat) :
    spur (t + 1) 0 (crank (t + 1) (W s (t + 1) n + 1))
      = (spur (t + 1) 1 (crank (t + 1) (n + 1))
        || veil (t + 1) (crank (t + 1) (n + 2))) := by
  cases hs1 : spur (t + 1) 1 (crank (t + 1) (n + 1)) with
  | true =>
      rw [the_spur_slides_to_the_wrap t s hg hf n hs1]
      rfl
  | false =>
      cases hv : veil (t + 1) (crank (t + 1) (n + 2)) with
      | true =>
          rw [the_veil_shades_the_wrap t s hg hf n hv]
          rfl
      | false =>
          cases hL : spur (t + 1) 0 (crank (t + 1) (W s (t + 1) n + 1)) with
          | false => rfl
          | true =>
              have h := the_wrap_names_its_two_seats t s hg hf n hL
              rw [hs1, hv] at h
              exact nomatch h

/-- info: 'Foam.Bridges.the_spur_snags_on_the_veil' does not depend on any axioms -/
#guard_msgs in #print axioms the_spur_snags_on_the_veil

theorem the_patron_chain_snags_on_the_veil (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n : Nat) :
    patron s (t + 1) 2 n = patron s (t + 1) 1 (W s (t + 1) n)
      + cond (veil (t + 1) (crank (t + 1) (n + 2))) 1 0 := by
  show coil (W s (t + 1)) 2 n - cond (spur (t + 1) 1 (crank (t + 1) (n + 1))) 1 0
    = coil (W s (t + 1)) 1 (W s (t + 1) n)
        - cond (spur (t + 1) 0 (crank (t + 1) (W s (t + 1) n + 1))) 1 0
      + cond (veil (t + 1) (crank (t + 1) (n + 2))) 1 0
  rw [the_spur_snags_on_the_veil t s hg hf n]
  cases hs1 : spur (t + 1) 1 (crank (t + 1) (n + 1)) with
  | true =>
      rw [the_spur_and_the_oncoming_veil_never_meet t s hg hf n hs1]
      rfl
  | false =>
      cases hv : veil (t + 1) (crank (t + 1) (n + 2)) with
      | false => rfl
      | true =>
          cases n with
          | zero => exact nomatch hv
          | succ m =>
              have hw := the_family_stays_awake t s hg hf m
              match a_tick_is_a_step (W s (t + 1) (m + 1)) hw with
              | ⟨w, hwd⟩ =>
                  have hA : 1 ≤ coil (W s (t + 1)) 2 (m + 1) := by
                    show 1 ≤ W s (t + 1) (W s (t + 1) (m + 1))
                    rw [hwd]
                    exact the_family_stays_awake t s hg hf w
                  show coil (W s (t + 1)) 2 (m + 1) - 0
                    = coil (W s (t + 1)) 2 (m + 1) - 1 + 1
                  exact (sub_one_back (coil (W s (t + 1)) 2 (m + 1)) hA).symm

/-- info: 'Foam.Bridges.the_patron_chain_snags_on_the_veil' does not depend on any axioms -/
#guard_msgs in #print axioms the_patron_chain_snags_on_the_veil

theorem the_walk_and_the_second_patron_square_the_couple (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n : Nat) :
    patron s (t + 1) 2 n + W s (t + 1) (n + 1)
      = groom s (t + 1) (W s (t + 1) n) + bride s (t + 1) (n + 1) := by
  rw [the_patron_chain_snags_on_the_veil t s hg hf n,
    the_patron_is_the_groom s (t + 1) (W s (t + 1) n)]
  show groom s (t + 1) (W s (t + 1) n) + cond (veil (t + 1) (crank (t + 1) (n + 2))) 1 0
      + W s (t + 1) (n + 1)
    = groom s (t + 1) (W s (t + 1) n)
      + (W s (t + 1) (n + 1) + cond (veil (t + 1) (crank (t + 1) (n + 2))) 1 0)
  rw [Nat.add_assoc (groom s (t + 1) (W s (t + 1) n))
    (cond (veil (t + 1) (crank (t + 1) (n + 2))) 1 0) (W s (t + 1) (n + 1))]
  rw [Nat.add_comm (cond (veil (t + 1) (crank (t + 1) (n + 2))) 1 0) (W s (t + 1) (n + 1))]

/-- info: 'Foam.Bridges.the_walk_and_the_second_patron_square_the_couple' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_and_the_second_patron_square_the_couple

theorem the_matrons_descend_from_the_bride (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) :
    ∀ (j : Nat), j + 1 ≤ t + 1 → ∀ (n : Nat),
      matron s (t + 1) (j + 1) n = bride s (t + 1) (coil (W s (t + 1)) j n)
  | 0, _, n => the_matron_is_the_bride s (t + 1) n
  | j + 1, hj, n => by
      rw [the_matron_speaks_one_altitude_down t j s hg hf hj n]
      exact the_matrons_descend_from_the_bride t s hg hf j
        (Nat.le_of_succ_le hj) (W s (t + 1) n)

theorem the_patrons_descend_from_the_second (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) :
    ∀ (j : Nat), j + 2 ≤ t + 1 → ∀ (n : Nat),
      patron s (t + 1) (j + 2) n = patron s (t + 1) 2 (coil (W s (t + 1)) j n)
  | 0, _, _ => rfl
  | j + 1, hj, n => by
      rw [the_patron_speaks_one_altitude_down t j s hg hf hj n]
      exact the_patrons_descend_from_the_second t s hg hf j
        (Nat.le_of_succ_le hj) (W s (t + 1) n)

/-- info: 'Foam.Bridges.the_matrons_descend_from_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms the_matrons_descend_from_the_bride

/-- info: 'Foam.Bridges.the_patrons_descend_from_the_second' does not depend on any axioms -/
#guard_msgs in #print axioms the_patrons_descend_from_the_second

theorem a_clocked_walk_wakes_stepping (f : Nat → Nat) (hc : Clocked f) : f 1 = 1 := by
  obtain ⟨c, h0, hs, hr⟩ := hc
  have h1 : c 0 + 0 + 1 ≤ c 1 := by
    have h := hs 0
    rw [h0] at h ⊢
    exact h
  have h2 := hr 0 0 h1
  rw [h0] at h2
  exact h2

/-- info: 'Foam.Bridges.a_clocked_walk_wakes_stepping' does not depend on any axioms -/
#guard_msgs in #print axioms a_clocked_walk_wakes_stepping

theorem the_groom_oversleeps (t : Nat) (s : Nat → Nat) (hf : Floored (t + 1) s) :
    groom s (t + 1) 1 = 0 := by
  show s (t + 1) + 0 - 1 = 0
  rw [hf t (Nat.le_succ t)]

theorem the_groom_reads_no_clock (t : Nat) (s : Nat → Nat) (hf : Floored (t + 1) s) :
    ¬ Clocked (groom s (t + 1)) := fun hc => by
  have h1 := a_clocked_walk_wakes_stepping (groom s (t + 1)) hc
  rw [the_groom_oversleeps t s hf] at h1
  exact nomatch h1

theorem the_bride_reads_no_page (t : Nat) (s : Nat → Nat) :
    ¬ Paged (bride s (t + 1)) := fun hp => by
  have h := a_paged_walk_never_outruns_the_count (bride s (t + 1)) hp 0
  rw [the_family_bride_wakes_lit t s] at h
  exact absurd h (Nat.not_succ_le_zero 0)

theorem the_groom_reads_no_page (t : Nat) (s : Nat → Nat) (hf : Floored (t + 1) s) :
    ¬ Paged (groom s (t + 1)) := fun hp => by
  have h := a_paged_walk_holds_the_half (groom s (t + 1)) hp 1
  rw [the_groom_oversleeps t s hf] at h
  exact absurd h (Nat.not_succ_le_zero 0)

theorem the_matron_reads_no_page (t j : Nat) (s : Nat → Nat) :
    ¬ Paged (matron s (t + 1) j) := fun hp => by
  have h := a_paged_walk_never_outruns_the_count (matron s (t + 1) j) hp 0
  rw [the_matron_wakes_lit t j s] at h
  exact absurd h (Nat.not_succ_le_zero 0)

theorem the_household_leans_out_of_space (t : Nat) (s : Nat → Nat)
    (hf : Floored (t + 1) s) :
    ¬ Paged (bride s (t + 1)) ∧ ¬ Paged (groom s (t + 1)) :=
  ⟨the_bride_reads_no_page t s, the_groom_reads_no_page t s hf⟩

/-- info: 'Foam.Bridges.the_groom_oversleeps' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_oversleeps

/-- info: 'Foam.Bridges.the_groom_reads_no_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_reads_no_clock

/-- info: 'Foam.Bridges.the_bride_reads_no_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_reads_no_page

/-- info: 'Foam.Bridges.the_groom_reads_no_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_groom_reads_no_page

/-- info: 'Foam.Bridges.the_matron_reads_no_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_matron_reads_no_page

/-- info: 'Foam.Bridges.the_household_leans_out_of_space' does not depend on any axioms -/
#guard_msgs in #print axioms the_household_leans_out_of_space

theorem the_second_patron_steps_back (t : Nat) (s : Nat → Nat)
    (hf : Floored (t + 2) s) :
    patron s (t + 2) 2 1 = 1 ∧ patron s (t + 2) 2 2 = 0 := by
  have hw1 : W s (t + 2) 1 = 1 := by
    show s (t + 2) + 0 = 1
    rw [hf (t + 1) (Nat.le_succ (t + 1))]
  have hw2 : W s (t + 2) 2 = 1 := by
    show s (t + 3) + 0 = 1
    rw [hf (t + 2) (Nat.le_refl (t + 2))]
  constructor
  · show W s (t + 2) (W s (t + 2) 1) - 0 = 1
    rw [hw1, hw1]
  · have hc3 : crank (t + 2) 3 = [2] := by
      show tick (t + 2) (crank (t + 2) 2) = [2]
      have hc2 : crank (t + 2) 2 = [1] := rfl
      rw [hc2]
      exact the_tick_climbs_the_floor (t + 2) 1 (Nat.succ_le_succ (Nat.zero_le (t + 1)))
    show coil (W s (t + 2)) 2 2 - cond (spur (t + 2) 1 (crank (t + 2) 3)) 1 0 = 0
    rw [hc3]
    show W s (t + 2) (W s (t + 2) 2) - 1 = 0
    rw [hw2, hw1]

theorem the_second_patron_reads_no_clock (t : Nat) (s : Nat → Nat)
    (hf : Floored (t + 2) s) : ¬ Clocked (patron s (t + 2) 2) := fun hc => by
  have h := a_clocked_walk_never_steps_back (patron s (t + 2) 2) hc 0
  rw [(the_second_patron_steps_back t s hf).1,
    (the_second_patron_steps_back t s hf).2] at h
  exact absurd h (Nat.not_succ_le_zero 0)

/-- info: 'Foam.Bridges.the_second_patron_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_patron_steps_back

/-- info: 'Foam.Bridges.the_second_patron_reads_no_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_patron_reads_no_clock

def btime (s : Nat → Nat) (e v : Nat) : Nat :=
  v + coil (W s e) (e - 1) (groom s e v)

theorem the_first_hour_strikes_at_two (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : stime s (t + 1) 1 = 2 := by
  rw [the_family_beat_reads_the_gate t s hg hf 0]
  rfl

/-- info: 'Foam.Bridges.the_first_hour_strikes_at_two' does not depend on any axioms -/
#guard_msgs in #print axioms the_first_hour_strikes_at_two

theorem the_bride_never_steps_back (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat) :
    bride s (t + 1) n ≤ bride s (t + 1) (n + 1) := by
  cases hv : veil (t + 1) (crank (t + 1) (n + 1)) with
  | false =>
      have h1 : bride s (t + 1) n = W s (t + 1) n := by
        show W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0 = W s (t + 1) n
        rw [hv]
        rfl
      rw [h1]
      exact Nat.le_trans (the_family_never_steps_back t s hg hf n)
        (Nat.le_add_right (W s (t + 1) (n + 1))
          (cond (veil (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0))
  | true =>
      have h1 : bride s (t + 1) n = W s (t + 1) n + 1 := by
        show W s (t + 1) n + cond (veil (t + 1) (crank (t + 1) (n + 1))) 1 0
          = W s (t + 1) n + 1
        rw [hv]
        rfl
      cases hcp : crank (t + 1) (n + 1) with
      | nil => rw [hcp] at hv; exact nomatch hv
      | cons g gs =>
          cases gs with
          | cons g₂ gs₂ =>
              rw [hcp, the_veil_skips_two_strides (t + 1) g g₂ gs₂] at hv
              exact nomatch hv
          | nil =>
              cases g with
              | zero =>
                  have hd := the_dial_reads_true (t + 1) s hg hf (n + 1)
                  rw [hcp] at hd
                  have hd' : s (t + 2) = n + 1 := hd
                  rw [hf (t + 1) (Nat.le_refl (t + 1))] at hd'
                  have hn0 : 0 = n := Nat.succ.inj hd'
                  have hb1 : bride s (t + 1) 1 = 1 := by
                    show s (t + 1) + 0 + cond (veil (t + 1) (crank (t + 1) 2)) 1 0 = 1
                    rw [hf t (Nat.le_succ t)]
                    rfl
                  rw [← hn0, the_family_bride_wakes_lit t s, hb1]
                  exact Nat.le_refl 1
              | succ p =>
                  rw [hcp] at hv
                  have hbr : (brand (t + 1) p).2 = 1 := Nat.eq_of_beq_eq_true hv
                  have hstep := a_branded_crossing_steps_the_walk t s hg hf n p 0 hcp hbr
                    (Nat.succ_le_succ (Nat.zero_le t))
                  rw [h1, hstep]
                  exact Nat.le_add_right (W s (t + 1) (n + 1))
                    (cond (veil (t + 1) (crank (t + 1) (n + 1 + 1))) 1 0)

theorem the_bride_walks_forward (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (d a : Nat), bride s (t + 1) a ≤ bride s (t + 1) (a + d)
  | 0, a => Nat.le_refl (bride s (t + 1) a)
  | d + 1, a => Nat.le_trans (the_bride_walks_forward t s hg hf d a)
      (the_bride_never_steps_back t s hg hf (a + d))

/-- info: 'Foam.Bridges.the_bride_never_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_never_steps_back

/-- info: 'Foam.Bridges.the_bride_walks_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_walks_forward

theorem coil_ride_shuffle (a b : Nat) : a + (b + 2) + a + 2 = a + (b + a + 2) + 2 := by
  have h2 : b + 1 + a = b + a + 1 := seat_shuffles b a
  have h1 : b + 1 + 1 + a = b + 1 + a + 1 := seat_shuffles (b + 1) a
  rw [h2] at h1
  have h : b + 2 + a = b + a + 2 := h1
  rw [Nat.add_assoc a (b + 2) a, h]

/-- info: 'Foam.Bridges.coil_ride_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms coil_ride_shuffle

theorem the_brides_hour_docks_the_sash (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) :
    btime s (t + 1) v + cond (sash (t + 1) (crank (t + 1) (v + 1))) 1 0
      = stime s (t + 1) v := by
  cases hσ : sash (t + 1) (crank (t + 1) (v + 1)) with
  | false =>
      have hgv : groom s (t + 1) v = W s (t + 1) v := by
        show W s (t + 1) v - cond (sash (t + 1) (crank (t + 1) (v + 1))) 1 0 = W s (t + 1) v
        rw [hσ]
        rfl
      show v + coil (W s (t + 1)) t (groom s (t + 1) v) + 0 = stime s (t + 1) v
      rw [hgv]
      have hst : stime s (t + 1) v = v + coil (W s (t + 1)) (t + 1) v :=
        the_family_clock_adds_the_deep_shadow t s hg hf v
      rw [hst]
      rfl
  | true =>
      match the_sash_finds_its_beacon (t + 1) (crank (t + 1) (v + 1)) hσ with
      | ⟨k, hpage, hres⟩ =>
          have hbrk : (brand (t + 1) k).2 = 0 := Nat.eq_of_beq_eq_true hres
          have hrungs : rungs (t + 1) (brand (t + 1) k).1 = k := by
            have h := the_brand_reads_the_rungs (t + 1) k
            rw [hbrk] at h
            exact h
          cases hq : (brand (t + 1) k).1 with
          | zero =>
              rw [hq] at hrungs
              have hk0 : (0 : Nat) = k := hrungs
              have hpage' : crank (t + 1) (v + 1) = [1] := by
                rw [hpage, ← hk0]
              have hd := the_dial_reads_true (t + 1) s hg hf (v + 1)
              rw [hpage'] at hd
              have hd' : s (t + 3) = v + 1 := hd
              rw [the_first_flight_reads_two t s hg hf] at hd'
              have hv1 : 1 = v := Nat.succ.inj hd'
              have hg1 : groom s (t + 1) v = 0 := by
                rw [← hv1]
                exact the_groom_oversleeps t s hf
              show v + coil (W s (t + 1)) t (groom s (t + 1) v) + 1 = stime s (t + 1) v
              rw [hg1, the_coil_rests_at_zero t s t, ← hv1,
                the_first_hour_strikes_at_two t s hg hf]
          | succ q₁ =>
              have hk : rungs (t + 1) q₁ + t + 2 = k := by
                rw [hq] at hrungs
                exact hrungs
              have hv1 : v + 1 = s (t + (k + 1) + 2) :=
                a_crossing_reads_its_stair t s hg hf v (k + 1) hpage
              have hrest : W s (t + 1) v = W s (t + 1) (v + 1) :=
                a_wrapped_crossing_rests_the_walk t s hg hf v k hpage hbrk
              have hWv : W s (t + 1) v = s (t + k + 2) := by
                rw [hrest, hv1]
                exact the_family_beacon_slides t (k + 1) s hg hf
              have hglow : 1 ≤ s (t + k + 2) := a_grammar_glows (t + 1) s hg hf (t + k + 1)
              match a_tick_is_a_step (s (t + k + 2)) hglow with
              | ⟨x, hx⟩ =>
                  have hgv : groom s (t + 1) v = x := by
                    show W s (t + 1) v
                        - cond (sash (t + 1) (crank (t + 1) (v + 1))) 1 0 = x
                    rw [hσ, hWv, hx]
                    rfl
                  have hcl : brand (t + 1) (rungs (t + 1) q₁ + t + 1) = (q₁, t + 1) :=
                    the_brand_climbs_the_rungs (t + 1) q₁ (t + 1) (Nat.le_refl (t + 1))
                  have hbrp : (brand (t + 1) (rungs (t + 1) q₁ + t + 1)).2 = t + 1 := by
                    rw [hcl]
                  have hix : rungs (t + 1) q₁ + t + 1 + t + 3
                      = t + (rungs (t + 1) q₁ + t + 2) + 2 := by
                    rw [seat_shuffles (rungs (t + 1) q₁ + t) t]
                    exact congrArg (· + 4) (Nat.add_comm (rungs (t + 1) q₁ + t) t)
                  have hx' : x + 1 = s (rungs (t + 1) q₁ + t + 1 + t + 3) := by
                    rw [hix]
                    rw [← hk] at hx
                    exact hx.symm
                  have hwound := the_wounded_beacon_rides_the_coil t s hg hf
                    (rungs (t + 1) q₁ + t + 1) x hbrp hx'
                  have hride := the_beacon_rides_the_coil t s hg hf t
                    (rungs (t + 1) q₁ + 2)
                  rw [coil_ride_shuffle t (rungs (t + 1) q₁)] at hride
                  rw [hk] at hride
                  have hix3 : t + (rungs (t + 1) q₁ + 2) + 2
                      = rungs (t + 1) q₁ + t + 1 + 3 :=
                    congrArg (· + 4) (Nat.add_comm t (rungs (t + 1) q₁))
                  rw [hix3] at hride
                  have hst : stime s (t + 1) v
                      = v + coil (W s (t + 1)) t (W s (t + 1) v) :=
                    the_family_clock_adds_the_deep_shadow t s hg hf v
                  rw [hWv] at hst
                  show v + coil (W s (t + 1)) t (groom s (t + 1) v) + 1
                    = stime s (t + 1) v
                  rw [hgv, hst, hride, ← hwound]
                  rfl

/-- info: 'Foam.Bridges.the_brides_hour_docks_the_sash' does not depend on any axioms -/
#guard_msgs in #print axioms the_brides_hour_docks_the_sash

theorem the_bride_walks_at_the_first_beat (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) :
    bride s (t + 1) (btime s (t + 1) v + 1) = v + 1 := by
  cases hσ : sash (t + 1) (crank (t + 1) (v + 1)) with
  | false =>
      have hbt : btime s (t + 1) v = stime s (t + 1) v := by
        have h := the_brides_hour_docks_the_sash t s hg hf v
        rw [hσ] at h
        exact h
      rw [hbt]
      show W s (t + 1) (stime s (t + 1) v + 1)
          + cond (veil (t + 1) (crank (t + 1) (stime s (t + 1) v + 1 + 1))) 1 0 = v + 1
      rw [the_family_walks_at_the_first_beat t s hg hf v]
      cases hr : roomy (t + 1) (crank (t + 1) v) with
      | true =>
          have hb2 : stime s (t + 1) (v + 1) = stime s (t + 1) v + 2 := by
            rw [the_family_beat_reads_the_gate t s hg hf v, hr]
            rfl
          have hb2' : stime s (t + 1) v + 1 + 1 = stime s (t + 1) (v + 1) := hb2.symm
          have hcc : crank (t + 1) (stime s (t + 1) v + 1 + 1)
              = lift 1 (crank (t + 1) (v + 1)) := by
            rw [hb2']
            exact the_family_hour_writes_the_page_above t s hg hf (v + 1)
          rw [hcc]
          cases hcv : crank (t + 1) (v + 1) with
          | nil => rfl
          | cons a as =>
              cases as with
              | cons a₂ as₂ =>
                  show v + 1
                      + cond (veil (t + 1) ((a + 1) :: a₂ :: as₂)) 1 0 = v + 1
                  rw [the_veil_skips_two_strides (t + 1) (a + 1) a₂ as₂]
                  rfl
              | nil =>
                  show v + 1 + cond (Nat.beq (brand (t + 1) a).2 1) 1 0 = v + 1
                  cases hba : Nat.beq (brand (t + 1) a).2 1 with
                  | false => rfl
                  | true =>
                      have hbra : (brand (t + 1) a).2 = 1 := Nat.eq_of_beq_eq_true hba
                      cases a with
                      | zero => exact nomatch hbra
                      | succ a₁ =>
                          have hbr0 : (brand (t + 1) a₁).2 = 0 :=
                            the_brand_steps_back (t + 1) a₁ 0 hbra
                          have hpv : crank (t + 1) v
                              = 0 :: unfurl (t + 1) (brand (t + 1) a₁).1 [] := by
                            rw [the_crank_steps_back (t + 1) v, hcv,
                              the_untick_opens_the_purse (t + 1) a₁, hbr0]
                          rw [hpv] at hr
                          exact nomatch hr
      | false =>
          have hb1 : stime s (t + 1) (v + 1) = stime s (t + 1) v + 1 := by
            rw [the_family_beat_reads_the_gate t s hg hf v, hr]
            rfl
          have hb1' : stime s (t + 1) v + 1 = stime s (t + 1) (v + 1) := hb1.symm
          have hcc : crank (t + 1) (stime s (t + 1) v + 1 + 1)
              = tick (t + 1) (lift 1 (crank (t + 1) (v + 1))) := by
            rw [hb1']
            show tick (t + 1) (crank (t + 1) (stime s (t + 1) (v + 1)))
              = tick (t + 1) (lift 1 (crank (t + 1) (v + 1)))
            rw [the_family_hour_writes_the_page_above t s hg hf (v + 1)]
          rw [hcc]
          cases hbig : veil (t + 1) (tick (t + 1) (lift 1 (crank (t + 1) (v + 1)))) with
          | false => rfl
          | true =>
              have hsp : Spread (t + 1) (lift 1 (crank (t + 1) (v + 1))) :=
                the_lift_keeps_the_spread (t + 1) 1 (crank (t + 1) (v + 1))
                  (the_dial_keeps_the_spread (t + 1) (v + 1))
              have hut := the_untick_comes_home (t + 1)
                (lift 1 (crank (t + 1) (v + 1))) hsp
              match the_veil_finds_its_beacon (t + 1)
                  (tick (t + 1) (lift 1 (crank (t + 1) (v + 1)))) hbig with
              | Or.inl h0 =>
                  rw [h0] at hut
                  cases hcv : crank (t + 1) (v + 1) with
                  | nil =>
                      exact absurd hcv
                        (the_tick_never_blanks (t + 1) (crank (t + 1) v))
                  | cons a as =>
                      rw [hcv] at hut
                      exact nomatch hut
              | Or.inr hex =>
                  match hex with
                  | ⟨x, hx, hclx⟩ =>
                      rw [hx] at hut
                      have hclx' : (brand (t + 1) x).2 = 1 := Nat.eq_of_beq_eq_true hclx
                      rw [the_untick_opens_the_purse (t + 1) x, hclx'] at hut
                      cases hcv : crank (t + 1) (v + 1) with
                      | nil =>
                          exact absurd hcv
                            (the_tick_never_blanks (t + 1) (crank (t + 1) v))
                      | cons a as =>
                          rw [hcv] at hut
                          have hut' : 1 :: unfurl (t + 1) (brand (t + 1) x).1 []
                              = (a + 1) :: as := hut
                          injection hut' with h1 h2
                          have ha0 : (0 : Nat) = a := Nat.succ.inj h1
                          have hpv : crank (t + 1) v
                              = unfurl (t + 1) 0 (unfurl (t + 1) (brand (t + 1) x).1 []) := by
                            rw [the_crank_steps_back (t + 1) v, hcv, ← ha0, h2]
                            rfl
                          cases hq : (brand (t + 1) x).1 with
                          | zero =>
                              rw [hq] at hpv
                              have hpv' : crank (t + 1) v = [] := hpv
                              rw [hpv'] at hr
                              exact nomatch hr
                          | succ q₁ =>
                              rw [hq] at hpv
                              have hpv' : crank (t + 1) v
                                  = (t + 2) :: unfurl (t + 1) q₁ [] := hpv
                              rw [hpv'] at hr
                              have hr' : Nat.ble (t + 1) (t + 2) = false := hr
                              rw [Nat.ble_eq_true_of_le (Nat.le_succ (t + 1))] at hr'
                              exact nomatch hr'
  | true =>
      have hbt : btime s (t + 1) v + 1 = stime s (t + 1) v := by
        have h := the_brides_hour_docks_the_sash t s hg hf v
        rw [hσ] at h
        exact h
      rw [hbt]
      show W s (t + 1) (stime s (t + 1) v)
          + cond (veil (t + 1) (crank (t + 1) (stime s (t + 1) v + 1))) 1 0 = v + 1
      rw [the_family_arrives_on_the_hour t s hg hf v]
      match the_sash_finds_its_beacon (t + 1) (crank (t + 1) (v + 1)) hσ with
      | ⟨k, hpage, hres⟩ =>
          have hbrk : (brand (t + 1) k).2 = 0 := Nat.eq_of_beq_eq_true hres
          have hpv : crank (t + 1) v = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
            rw [the_crank_steps_back (t + 1) v, hpage,
              the_untick_opens_the_purse (t + 1) k, hbrk]
          have hcc : crank (t + 1) (stime s (t + 1) v + 1)
              = [rungs (t + 1) (brand (t + 1) k).1 + 2] := by
            show tick (t + 1) (crank (t + 1) (stime s (t + 1) v))
              = [rungs (t + 1) (brand (t + 1) k).1 + 2]
            rw [the_family_hour_writes_the_page_above t s hg hf v, hpv]
            show tick (t + 1) (1 :: unfurl (t + 1) (brand (t + 1) k).1 [])
              = [rungs (t + 1) (brand (t + 1) k).1 + 2]
            exact the_tick_tops_the_purse (t + 1) 0 (brand (t + 1) k).1
              (Nat.succ_le_succ (Nat.zero_le t))
          rw [hcc]
          show v + cond (Nat.beq
              (brand (t + 1) (rungs (t + 1) (brand (t + 1) k).1 + 1)).2 1) 1 0 = v + 1
          rw [the_brand_climbs_the_rungs (t + 1) (brand (t + 1) k).1 1
            (Nat.succ_le_succ (Nat.zero_le t))]
          rfl

/-- info: 'Foam.Bridges.the_bride_walks_at_the_first_beat' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_walks_at_the_first_beat

theorem the_bride_arrives_on_her_hour (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) :
    bride s (t + 1) (btime s (t + 1) (v + 1)) = v + 1 := by
  cases hσ : sash (t + 1) (crank (t + 1) (v + 1 + 1)) with
  | false =>
      have hbt : btime s (t + 1) (v + 1) = stime s (t + 1) (v + 1) := by
        have h := the_brides_hour_docks_the_sash t s hg hf (v + 1)
        rw [hσ] at h
        exact h
      rw [hbt]
      show W s (t + 1) (stime s (t + 1) (v + 1))
          + cond (veil (t + 1) (crank (t + 1) (stime s (t + 1) (v + 1) + 1))) 1 0 = v + 1
      rw [the_family_arrives_on_the_hour t s hg hf (v + 1)]
      have hcc : crank (t + 1) (stime s (t + 1) (v + 1) + 1)
          = tick (t + 1) (lift 1 (crank (t + 1) (v + 1))) := by
        show tick (t + 1) (crank (t + 1) (stime s (t + 1) (v + 1)))
          = tick (t + 1) (lift 1 (crank (t + 1) (v + 1)))
        rw [the_family_hour_writes_the_page_above t s hg hf (v + 1)]
      rw [hcc]
      cases hbig : veil (t + 1) (tick (t + 1) (lift 1 (crank (t + 1) (v + 1)))) with
      | false => rfl
      | true =>
          have hsp : Spread (t + 1) (lift 1 (crank (t + 1) (v + 1))) :=
            the_lift_keeps_the_spread (t + 1) 1 (crank (t + 1) (v + 1))
              (the_dial_keeps_the_spread (t + 1) (v + 1))
          have hut := the_untick_comes_home (t + 1)
            (lift 1 (crank (t + 1) (v + 1))) hsp
          match the_veil_finds_its_beacon (t + 1)
              (tick (t + 1) (lift 1 (crank (t + 1) (v + 1)))) hbig with
          | Or.inl h0 =>
              rw [h0] at hut
              cases hcv : crank (t + 1) (v + 1) with
              | nil =>
                  exact absurd hcv (the_tick_never_blanks (t + 1) (crank (t + 1) v))
              | cons a as =>
                  rw [hcv] at hut
                  exact nomatch hut
          | Or.inr hex =>
              match hex with
              | ⟨x, hx, hclx⟩ =>
                  rw [hx] at hut
                  have hclx' : (brand (t + 1) x).2 = 1 := Nat.eq_of_beq_eq_true hclx
                  rw [the_untick_opens_the_purse (t + 1) x, hclx'] at hut
                  cases hcv : crank (t + 1) (v + 1) with
                  | nil =>
                      exact absurd hcv
                        (the_tick_never_blanks (t + 1) (crank (t + 1) v))
                  | cons a as =>
                      rw [hcv] at hut
                      have hut' : 1 :: unfurl (t + 1) (brand (t + 1) x).1 []
                          = (a + 1) :: as := hut
                      injection hut' with h1 h2
                      have ha0 : (0 : Nat) = a := Nat.succ.inj h1
                      have hc2 : crank (t + 1) (v + 1 + 1)
                          = [rungs (t + 1) (brand (t + 1) x).1 + 1] := by
                        show tick (t + 1) (crank (t + 1) (v + 1))
                          = [rungs (t + 1) (brand (t + 1) x).1 + 1]
                        rw [hcv, ← ha0, ← h2]
                        show lift 1 (perch (t + 1)
                            (unfurl (t + 1) (brand (t + 1) x).1 []))
                          = [rungs (t + 1) (brand (t + 1) x).1 + 1]
                        rw [the_perch_comes_home (t + 1) (brand (t + 1) x).1 [] True.intro]
                        rfl
                      rw [hc2] at hσ
                      have hσ' : Nat.beq
                          (brand (t + 1) (rungs (t + 1) (brand (t + 1) x).1)).2 0
                          = false := hσ
                      rw [the_brand_mounts_the_rungs (t + 1) (brand (t + 1) x).1] at hσ'
                      exact nomatch hσ'
  | true =>
      match the_sash_finds_its_beacon (t + 1) (crank (t + 1) (v + 1 + 1)) hσ with
      | ⟨k, hpage, hres⟩ =>
          have hbrk : (brand (t + 1) k).2 = 0 := Nat.eq_of_beq_eq_true hres
          have hpv1 : crank (t + 1) (v + 1)
              = 0 :: unfurl (t + 1) (brand (t + 1) k).1 [] := by
            rw [the_crank_steps_back (t + 1) (v + 1), hpage,
              the_untick_opens_the_purse (t + 1) k, hbrk]
          have hbt : btime s (t + 1) (v + 1) + 1 = stime s (t + 1) (v + 1) := by
            have h := the_brides_hour_docks_the_sash t s hg hf (v + 1)
            rw [hσ] at h
            exact h
          cases hq : (brand (t + 1) k).1 with
          | zero =>
              rw [hq] at hpv1
              have hpv1' : crank (t + 1) (v + 1) = [0] := hpv1
              have hd := the_dial_reads_true (t + 1) s hg hf (v + 1)
              rw [hpv1'] at hd
              have hd' : s (t + 2) = v + 1 := hd
              rw [hf (t + 1) (Nat.le_refl (t + 1))] at hd'
              have hv0 : 0 = v := Nat.succ.inj hd'
              rw [← hv0] at hbt ⊢
              rw [the_first_hour_strikes_at_two t s hg hf] at hbt
              have hbt1 : btime s (t + 1) 1 = 1 := Nat.succ.inj hbt
              rw [hbt1]
              show s (t + 1) + 0 + cond (veil (t + 1) (crank (t + 1) 2)) 1 0 = 0 + 1
              rw [hf t (Nat.le_succ t)]
              rfl
          | succ q₁ =>
              have hpv0 : crank (t + 1) v = (t + 2) :: unfurl (t + 1) q₁ [] := by
                rw [the_crank_steps_back (t + 1) v, hpv1, hq]
                rfl
              have hroomy : roomy (t + 1) (crank (t + 1) v) = true := by
                rw [hpv0]
                exact Nat.ble_eq_true_of_le (Nat.le_succ (t + 1))
              have hbeat : stime s (t + 1) (v + 1) = stime s (t + 1) v + 2 := by
                rw [the_family_beat_reads_the_gate t s hg hf v, hroomy]
                rfl
              rw [hbeat] at hbt
              have hbt' : btime s (t + 1) (v + 1) = stime s (t + 1) v + 1 :=
                Nat.succ.inj hbt
              rw [hbt']
              show W s (t + 1) (stime s (t + 1) v + 1)
                  + cond (veil (t + 1)
                    (crank (t + 1) (stime s (t + 1) v + 1 + 1))) 1 0 = v + 1
              rw [the_family_walks_at_the_first_beat t s hg hf v]
              have hb2' : stime s (t + 1) v + 1 + 1 = stime s (t + 1) (v + 1) :=
                hbeat.symm
              have hcc : crank (t + 1) (stime s (t + 1) v + 1 + 1)
                  = 1 :: unfurl (t + 1) (q₁ + 1) [] := by
                rw [hb2']
                rw [the_family_hour_writes_the_page_above t s hg hf (v + 1), hpv1, hq]
                rfl
              rw [hcc]
              show v + 1
                  + cond (veil (t + 1) (1 :: (t + 1) :: unfurl (t + 1) q₁ [])) 1 0
                = v + 1
              rw [the_veil_skips_two_strides (t + 1) 1 (t + 1) (unfurl (t + 1) q₁ [])]
              rfl

/-- info: 'Foam.Bridges.the_bride_arrives_on_her_hour' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_arrives_on_her_hour

theorem the_brides_clock_never_stalls (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (v : Nat) :
    btime s (t + 1) v < btime s (t + 1) (v + 1) := by
  cases Nat.decLe (btime s (t + 1) v + 1) (btime s (t + 1) (v + 1)) with
  | isTrue h => exact h
  | isFalse h =>
      have hle : btime s (t + 1) (v + 1) ≤ btime s (t + 1) v :=
        Nat.le_of_succ_le_succ (Nat.gt_of_not_le h)
      match Nat.le.dest (Nat.succ_le_succ hle) with
      | ⟨d, hd⟩ =>
          have hm := the_bride_walks_forward t s hg hf d (btime s (t + 1) (v + 1) + 1)
          rw [hd, the_bride_walks_at_the_first_beat t s hg hf (v + 1),
            the_bride_walks_at_the_first_beat t s hg hf v] at hm
          exact absurd hm (Nat.not_succ_le_self (v + 1))

theorem the_bride_reads_her_hours (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (v i : Nat),
    btime s (t + 1) v + i + 1 ≤ btime s (t + 1) (v + 1) →
      bride s (t + 1) (btime s (t + 1) v + i + 1) = v + 1 := by
  intro v i h
  have hup : bride s (t + 1) (btime s (t + 1) v + i + 1) ≤ v + 1 := by
    match Nat.le.dest h with
    | ⟨d, hd⟩ =>
        have h1 := the_bride_walks_forward t s hg hf d (btime s (t + 1) v + i + 1)
        rw [hd, the_bride_arrives_on_her_hour t s hg hf v] at h1
        exact h1
  have hdn : v + 1 ≤ bride s (t + 1) (btime s (t + 1) v + i + 1) := by
    have h2 := the_bride_walks_forward t s hg hf i (btime s (t + 1) v + 1)
    rw [seat_shuffles (btime s (t + 1) v) i] at h2
    rw [the_bride_walks_at_the_first_beat t s hg hf v] at h2
    exact h2
  exact Nat.le_antisymm hup hdn

theorem the_bride_is_clocked (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : Clocked (bride s (t + 1)) := by
  refine ⟨btime s (t + 1), ?_, the_brides_clock_never_stalls t s hg hf,
    the_bride_reads_her_hours t s hg hf⟩
  show 0 + coil (W s (t + 1)) t 0 = 0
  rw [the_coil_rests_at_zero t s t]

/-- info: 'Foam.Bridges.the_brides_clock_never_stalls' does not depend on any axioms -/
#guard_msgs in #print axioms the_brides_clock_never_stalls

/-- info: 'Foam.Bridges.the_bride_reads_her_hours' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_reads_her_hours

/-- info: 'Foam.Bridges.the_bride_is_clocked' does not depend on any axioms -/
#guard_msgs in #print axioms the_bride_is_clocked

theorem time_keeps_only_the_bride (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) :
    Clocked (bride s (t + 1)) ∧ ¬ Clocked (groom s (t + 1)) :=
  ⟨the_bride_is_clocked t s hg hf, the_groom_reads_no_clock t s hf⟩

/-- info: 'Foam.Bridges.time_keeps_only_the_bride' does not depend on any axioms -/
#guard_msgs in #print axioms time_keeps_only_the_bride

theorem the_hours_march_forward (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) : ∀ (d a : Nat), stime s (t + 1) a ≤ stime s (t + 1) (a + d)
  | 0, a => Nat.le_refl (stime s (t + 1) a)
  | d + 1, a => Nat.le_trans (the_hours_march_forward t s hg hf d a)
      (Nat.le_of_succ_le (the_family_clock_never_stalls t s hg hf (a + d)))

theorem a_clocked_walk_walks_the_register (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (f : Nat → Nat) (hc : Clocked f) :
    Clocked (fun n => f (W s (t + 1) n)) := by
  obtain ⟨c, h0, hs, hr⟩ := hc
  refine ⟨fun v => stime s (t + 1) (c v), ?_, ?_, ?_⟩
  · show stime s (t + 1) (c 0) = 0
    rw [h0]
    rfl
  · intro v
    match Nat.le.dest (hs v) with
    | ⟨d, hd⟩ =>
        have h1 := the_family_clock_never_stalls t s hg hf (c v)
        have h2 := the_hours_march_forward t s hg hf d (c v + 1)
        rw [hd] at h2
        exact Nat.le_trans h1 h2
  · intro v j h
    have hlow : c v + 1 ≤ W s (t + 1) (stime s (t + 1) (c v) + j + 1) := by
      have hm := the_family_walks_forward t s hg hf j (stime s (t + 1) (c v) + 1)
      rw [seat_shuffles (stime s (t + 1) (c v)) j,
        the_family_walks_at_the_first_beat t s hg hf (c v)] at hm
      exact hm
    have hhigh : W s (t + 1) (stime s (t + 1) (c v) + j + 1) ≤ c (v + 1) := by
      match Nat.le.dest h with
      | ⟨d2, hd2⟩ =>
          have hm := the_family_walks_forward t s hg hf d2
            (stime s (t + 1) (c v) + j + 1)
          rw [hd2, the_family_arrives_on_the_hour t s hg hf (c (v + 1))] at hm
          exact hm
    match Nat.le.dest hlow with
    | ⟨i, hi⟩ =>
        have hle : c v + i + 1 ≤ c (v + 1) := by
          rw [← seat_shuffles (c v) i, hi]
          exact hhigh
        have hread := hr v i hle
        show f (W s (t + 1) (stime s (t + 1) (c v) + j + 1)) = v + 1
        rw [← hi, seat_shuffles (c v) i]
        exact hread

/-- info: 'Foam.Bridges.the_hours_march_forward' does not depend on any axioms -/
#guard_msgs in #print axioms the_hours_march_forward

/-- info: 'Foam.Bridges.a_clocked_walk_walks_the_register' does not depend on any axioms -/
#guard_msgs in #print axioms a_clocked_walk_walks_the_register

theorem every_matron_reads_the_clock (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) :
    ∀ (j : Nat), j + 1 ≤ t + 1 → Clocked (matron s (t + 1) (j + 1))
  | 0, _ => by
      obtain ⟨c, h0, hs, hr⟩ := the_bride_is_clocked t s hg hf
      exact ⟨c, h0, hs, fun v i h => by
        rw [the_matron_is_the_bride s (t + 1) (c v + i + 1)]
        exact hr v i h⟩
  | j + 1, hj => by
      have ih := every_matron_reads_the_clock t s hg hf j (Nat.le_of_succ_le hj)
      obtain ⟨c, h0, hs, hr⟩ := a_clocked_walk_walks_the_register t s hg hf
        (matron s (t + 1) (j + 1)) ih
      exact ⟨c, h0, hs, fun v i h => by
        rw [the_matron_speaks_one_altitude_down t j s hg hf hj (c v + i + 1)]
        exact hr v i h⟩

/-- info: 'Foam.Bridges.every_matron_reads_the_clock' does not depend on any axioms -/
#guard_msgs in #print axioms every_matron_reads_the_clock

theorem time_tells_the_spouses_apart : Clocked F ∧ ¬ Clocked M := by
  constructor
  · obtain ⟨c, h0, hs, hr⟩ := the_bride_is_clocked 0 fibN
      the_golden_staircase_holds_the_gnomon the_golden_staircase_holds_the_floor
    exact ⟨c, h0, hs, fun v j h => by
      rw [← the_family_reseals_the_bride (c v + j + 1)]
      exact hr v j h⟩
  · intro hc
    have h1 := a_clocked_walk_wakes_stepping M hc
    have h2 : M 1 = 0 := by
      rw [← the_family_reseals_the_groom 1]
      exact the_groom_oversleeps 0 fibN the_golden_staircase_holds_the_floor
    rw [h2] at h1
    exact nomatch h1

/-- info: 'Foam.Bridges.time_tells_the_spouses_apart' does not depend on any axioms -/
#guard_msgs in #print axioms time_tells_the_spouses_apart

theorem the_brides_clock_hums :
    (btime herdN 2 0, btime herdN 2 1, btime herdN 2 2, btime herdN 2 3,
      btime herdN 2 4, btime herdN 2 5, btime herdN 2 6, btime herdN 2 7,
      btime herdN 2 8, btime herdN 2 9, btime herdN 2 10, btime herdN 2 11)
    = (0, 1, 3, 4, 6, 7, 9, 11, 12, 13, 15, 16) := rfl

/-- info: 'Foam.Bridges.the_brides_clock_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_brides_clock_hums

theorem the_shallow_stairs_count_themselves (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) :
    ∀ (k : Nat), k ≤ t + 1 → s (t + k + 2) = k + 1
  | 0, _ => the_rail_reads_one t s hf
  | k + 1, hk => by
      have h := gnomon_tn t s hg k
      rw [the_shallow_stairs_count_themselves t s hg hf k (Nat.le_of_succ_le hk),
        hf k (Nat.le_of_succ_le hk)] at h
      exact h

theorem every_shallow_count_is_a_crossing (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (k : Nat) (hk : k ≤ t + 1) :
    crank (t + 1) (k + 1) = [k] := by
  have h := the_crank_at_a_stair_number_is_one_stride (t + 1) k s hg hf
  rw [show t + 1 + k + 1 = t + k + 2 from congrArg (· + 1) (seat_shuffles t k),
    the_shallow_stairs_count_themselves t s hg hf k hk] at h
  exact h

theorem the_walk_descends_the_shallow_stairs (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (k : Nat) (hk : k ≤ t) :
    W s (t + 1) (k + 2) = k + 1 := by
  have hcr : crank (t + 1) (k + 2) = [k + 1] :=
    every_shallow_count_is_a_crossing t s hg hf (k + 1) (Nat.succ_le_succ hk)
  show assay s (t + 1) (crank (t + 1) (k + 2)) = k + 1
  rw [hcr]
  show s (t + 1 + k + 1) + 0 = k + 1
  rw [show t + 1 + k + 1 = t + k + 2 from congrArg (· + 1) (seat_shuffles t k),
    the_shallow_stairs_count_themselves t s hg hf k (Nat.le_trans hk (Nat.le_succ t))]

/-- info: 'Foam.Bridges.the_shallow_stairs_count_themselves' does not depend on any axioms -/
#guard_msgs in #print axioms the_shallow_stairs_count_themselves

/-- info: 'Foam.Bridges.every_shallow_count_is_a_crossing' does not depend on any axioms -/
#guard_msgs in #print axioms every_shallow_count_is_a_crossing

/-- info: 'Foam.Bridges.the_walk_descends_the_shallow_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_descends_the_shallow_stairs

theorem the_floor_wears_every_crest (e r : Nat) : crest e r [0] = true := rfl

theorem the_floor_wears_no_spur (e r : Nat) : spur e r [0] = false := rfl

theorem a_wrapped_crossing_pins_the_page_below (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n p : Nat)
    (hpage : crank (t + 1) (n + 1) = [p + 1]) (hbr : (brand (t + 1) p).2 = 0) :
    crank (t + 1) (W s (t + 1) n) = [p] := by
  have hrest := a_wrapped_crossing_rests_the_walk t s hg hf n p hpage hbr
  have hn1 : n + 1 = s (t + (p + 1) + 2) := a_crossing_reads_its_stair t s hg hf n (p + 1) hpage
  have hW1 : W s (t + 1) (n + 1) = s (t + p + 2) := by
    rw [hn1]
    exact the_family_beacon_slides t (p + 1) s hg hf
  rw [hrest, hW1]
  have h := the_crank_at_a_stair_number_is_one_stride (t + 1) p s hg hf
  have hix : t + 1 + p + 1 = t + p + 2 := congrArg (· + 1) (seat_shuffles t p)
  rw [hix] at h
  exact h

/-- info: 'Foam.Bridges.the_floor_wears_every_crest' does not depend on any axioms -/
#guard_msgs in #print axioms the_floor_wears_every_crest

/-- info: 'Foam.Bridges.the_floor_wears_no_spur' does not depend on any axioms -/
#guard_msgs in #print axioms the_floor_wears_no_spur

/-- info: 'Foam.Bridges.a_wrapped_crossing_pins_the_page_below' does not depend on any axioms -/
#guard_msgs in #print axioms a_wrapped_crossing_pins_the_page_below

theorem the_necklace_closes (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (n : Nat)
    (h0 : spur (t + 1) 0 (crank (t + 1) (n + 1)) = true) :
    crest (t + 1) (t + 1) (crank (t + 1) (W s (t + 1) n)) = true := by
  cases hc : crank (t + 1) (n + 1) with
  | nil => rw [hc] at h0; exact nomatch h0
  | cons g gs =>
      cases gs with
      | cons g₂ gs₂ =>
          rw [hc, the_spur_skips_two_strides (t + 1) 0 g g₂ gs₂] at h0
          exact nomatch h0
      | nil =>
          cases g with
          | zero => rw [hc] at h0; exact nomatch h0
          | succ p =>
              rw [hc] at h0
              have hbr : (brand (t + 1) p).2 = 0 := Nat.eq_of_beq_eq_true h0
              rw [a_wrapped_crossing_pins_the_page_below t s hg hf n p hc hbr]
              cases p with
              | zero => rfl
              | succ p₁ =>
                  show Nat.beq (brand (t + 1) p₁).2 (t + 1) = true
                  rw [the_brand_wraps_back (t + 1) p₁ hbr]
                  exact beq_mirrors (t + 1)

theorem the_crossings_hang_on_one_thread (t : Nat) (s : Nat → Nat)
    (hg : Gnomon (t + 1) s) (hf : Floored (t + 1) s) (n p : Nat)
    (hpage : crank (t + 1) (n + 1) = [p + 1]) :
    crank (t + 1) (W s (t + 1) n + cond (Nat.beq (brand (t + 1) p).2 0) 0 1) = [p] := by
  cases hb : Nat.beq (brand (t + 1) p).2 0 with
  | true =>
      have hbr : (brand (t + 1) p).2 = 0 := Nat.eq_of_beq_eq_true hb
      exact a_wrapped_crossing_pins_the_page_below t s hg hf n p hpage hbr
  | false =>
      cases hr2 : (brand (t + 1) p).2 with
      | zero =>
          rw [hr2] at hb
          exact nomatch hb
      | succ r =>
          have hlow := the_brand_stays_low (t + 1) p
          rw [hr2] at hlow
          exact a_branded_crossing_pins_the_walked_page t s hg hf n p r hpage hr2 hlow

/-- info: 'Foam.Bridges.the_necklace_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_necklace_closes

/-- info: 'Foam.Bridges.the_crossings_hang_on_one_thread' does not depend on any axioms -/
#guard_msgs in #print axioms the_crossings_hang_on_one_thread

theorem the_herd_necklace_hums :
    ((spur 2 0 (crank 2 2), crest 2 2 (crank 2 (W herdN 2 1)), crank 2 (W herdN 2 1)),
      (spur 2 0 (crank 2 6), crest 2 2 (crank 2 (W herdN 2 5)), crank 2 (W herdN 2 5)),
      (spur 2 0 (crank 2 19), crest 2 2 (crank 2 (W herdN 2 18)), crank 2 (W herdN 2 18)))
    = ((true, true, [0]), (true, true, [3]), (true, true, [6])) := rfl

/-- info: 'Foam.Bridges.the_herd_necklace_hums' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_necklace_hums

theorem the_deeper_patrons_step_back (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 2) s)
    (hf : Floored (t + 2) s) :
    ∀ (j : Nat), j + 2 ≤ t + 2 →
      patron s (t + 2) (j + 2) (j + 1) = 1 ∧ patron s (t + 2) (j + 2) (j + 2) = 0
  | 0, _ => the_second_patron_steps_back t s hf
  | j + 1, hj => by
      have ih := the_deeper_patrons_step_back t s hg hf j (Nat.le_of_succ_le hj)
      have hj' : j + 2 ≤ t + 1 := Nat.le_of_succ_le_succ hj
      have hw1 : W s (t + 2) (j + 2) = j + 1 :=
        the_walk_descends_the_shallow_stairs (t + 1) s hg hf j
          (Nat.le_of_succ_le (Nat.le_of_succ_le hj'))
      have hw2 : W s (t + 2) (j + 3) = j + 2 :=
        the_walk_descends_the_shallow_stairs (t + 1) s hg hf (j + 1)
          (Nat.le_of_succ_le hj')
      have hch1 : patron s (t + 2) (j + 3) (j + 2)
          = patron s (t + 2) (j + 2) (W s (t + 2) (j + 2)) :=
        the_patron_speaks_one_altitude_down (t + 1) j s hg hf hj (j + 2)
      have hch2 : patron s (t + 2) (j + 3) (j + 3)
          = patron s (t + 2) (j + 2) (W s (t + 2) (j + 3)) :=
        the_patron_speaks_one_altitude_down (t + 1) j s hg hf hj (j + 3)
      have h1 : patron s (t + 2) (j + 3) (j + 2) = 1 := by
        rw [hch1, hw1]
        exact ih.1
      have h2 : patron s (t + 2) (j + 3) (j + 3) = 0 := by
        rw [hch2, hw2]
        exact ih.2
      exact ⟨h1, h2⟩

theorem the_deeper_patrons_read_no_clock (t j : Nat) (s : Nat → Nat) (hg : Gnomon (t + 2) s)
    (hf : Floored (t + 2) s) (hj : j + 2 ≤ t + 2) :
    ¬ Clocked (patron s (t + 2) (j + 2)) := fun hc => by
  have h : patron s (t + 2) (j + 2) (j + 1) ≤ patron s (t + 2) (j + 2) (j + 2) :=
    a_clocked_walk_never_steps_back (patron s (t + 2) (j + 2)) hc j
  rw [(the_deeper_patrons_step_back t s hg hf j hj).1,
    (the_deeper_patrons_step_back t s hg hf j hj).2] at h
  exact absurd h (Nat.not_succ_le_zero 0)

/-- info: 'Foam.Bridges.the_deeper_patrons_step_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_deeper_patrons_step_back

/-- info: 'Foam.Bridges.the_deeper_patrons_read_no_clock' does not depend on any axioms -/
#guard_msgs in #print axioms the_deeper_patrons_read_no_clock

theorem no_patron_reads_the_clock (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 2) s)
    (hf : Floored (t + 2) s) :
    ∀ (j : Nat), j + 1 ≤ t + 2 → ¬ Clocked (patron s (t + 2) (j + 1))
  | 0, _ => fun hc => by
      obtain ⟨c, h0, hs, hr⟩ := hc
      exact the_groom_reads_no_clock (t + 1) s hf
        ⟨c, h0, hs, fun v i h => by
          rw [← the_patron_is_the_groom s (t + 2) (c v + i + 1)]
          exact hr v i h⟩
  | j + 1, hj => the_deeper_patrons_read_no_clock t j s hg hf hj

theorem time_tells_the_lines_apart (t j : Nat) (s : Nat → Nat) (hg : Gnomon (t + 2) s)
    (hf : Floored (t + 2) s) (hj : j + 1 ≤ t + 2) :
    Clocked (matron s (t + 2) (j + 1)) ∧ ¬ Clocked (patron s (t + 2) (j + 1)) :=
  ⟨every_matron_reads_the_clock (t + 1) s hg hf j hj,
    no_patron_reads_the_clock t s hg hf j hj⟩

/-- info: 'Foam.Bridges.no_patron_reads_the_clock' does not depend on any axioms -/
#guard_msgs in #print axioms no_patron_reads_the_clock

/-- info: 'Foam.Bridges.time_tells_the_lines_apart' does not depend on any axioms -/
#guard_msgs in #print axioms time_tells_the_lines_apart

theorem the_next_patrons_stumble :
    (patron (stair 3) 3 2 1, patron (stair 3) 3 2 2,
      patron (stair 3) 3 3 2, patron (stair 3) 3 3 3)
    = (1, 0, 1, 0) := rfl

/-- info: 'Foam.Bridges.the_next_patrons_stumble' does not depend on any axioms -/
#guard_msgs in #print axioms the_next_patrons_stumble

end Foam.Bridges
