import Foam.Int
import Foam.Ledger
import Foam.Golden
import Foam.Bridges.Zeckendorf

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

theorem add_shuffle (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, ← Nat.add_assoc]

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

/-- info: 'Foam.Bridges.add_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms add_shuffle

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

end Foam.Bridges
