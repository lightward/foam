import Foam.Int
import Foam.Ledger
import Foam.Golden
import Foam.Bridges.Zeckendorf
import Foam.Bridges.Narayana
import Foam.Bridges.Leibniz

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

end Foam.Bridges
