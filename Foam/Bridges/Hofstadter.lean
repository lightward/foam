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

end Foam.Bridges
