import Foam.Int
import Foam.Bridges.Zeckendorf
import Foam.Bridges.Narayana
import Foam.Bridges.Leibniz

namespace Foam.Bridges

def price (s : Nat → Nat) : Nat → List Bool → Nat
  | _, [] => 0
  | i, false :: ds => price s (i + 1) ds
  | i, true :: ds => s i + price s (i + 1) ds

def Gnomon (e : Nat) (s : Nat → Nat) : Prop :=
  ∀ n, s (n + e + 2) = s (n + e + 1) + s (n + 1)

def Floored (e : Nat) (s : Nat → Nat) : Prop :=
  ∀ k, k ≤ e → s (k + 1) = 1

def cleared : Nat → List Bool → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | _ + 1, true :: _ => false
  | e + 1, false :: ds => cleared e ds

def Gapped : Nat → List Bool → Prop
  | _, [] => True
  | e, false :: ds => Gapped e ds
  | e, true :: ds => cleared e ds = true ∧ Gapped e ds

def peg : Nat → Nat
  | 0 => 0
  | k + 1 => notch k

theorem the_peg_hangs_the_ruler (k : Nat) : peg (k + 1) = notch k := rfl

theorem the_ruler_holds_the_gnomon : Gnomon 0 peg := fun _ => rfl

theorem the_ruler_holds_the_floor : Floored 0 peg := fun k h =>
  match k, h with
  | 0, _ => rfl
  | k + 1, h => absurd h (Nat.not_succ_le_zero k)

theorem the_herd_holds_the_gnomon : Gnomon 2 herdN := fun n => herdN_gnomon (n + 1)

theorem the_herd_holds_the_floor : Floored 2 herdN := fun k h =>
  match k, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | k + 3, h =>
      absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h)) (Nat.not_succ_le_zero k)

/-- info: 'Foam.Bridges.the_peg_hangs_the_ruler' does not depend on any axioms -/
#guard_msgs in #print axioms the_peg_hangs_the_ruler

/-- info: 'Foam.Bridges.the_ruler_holds_the_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms the_ruler_holds_the_gnomon

/-- info: 'Foam.Bridges.the_ruler_holds_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_ruler_holds_the_floor

/-- info: 'Foam.Bridges.the_herd_holds_the_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_holds_the_gnomon

/-- info: 'Foam.Bridges.the_herd_holds_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_holds_the_floor

theorem seat_splits : ∀ (k e : Nat), k ≤ e ∨ ∃ m, k = m + e + 1
  | 0, e => Or.inl (Nat.zero_le e)
  | k + 1, 0 => Or.inr ⟨k, rfl⟩
  | k + 1, e + 1 =>
      match seat_splits k e with
      | Or.inl h => Or.inl (Nat.succ_le_succ h)
      | Or.inr ⟨m, hm⟩ => Or.inr ⟨m, congrArg (· + 1) hm⟩

theorem at_the_rail : ∀ (k e : Nat), k ≤ e → k + 1 ≤ e ∨ k = e
  | 0, 0, _ => Or.inr rfl
  | 0, e + 1, _ => Or.inl (Nat.succ_le_succ (Nat.zero_le e))
  | k + 1, 0, h => absurd h (Nat.not_succ_le_zero k)
  | k + 1, e + 1, h =>
      match at_the_rail k e (Nat.le_of_succ_le_succ h) with
      | Or.inl h' => Or.inl (Nat.succ_le_succ h')
      | Or.inr h' => Or.inr (congrArg (· + 1) h')

theorem seat_shuffles : ∀ (a b : Nat), a + 1 + b = a + b + 1
  | _, 0 => rfl
  | a, b + 1 => congrArg (· + 1) (seat_shuffles a b)

/-- info: 'Foam.Bridges.seat_splits' does not depend on any axioms -/
#guard_msgs in #print axioms seat_splits

/-- info: 'Foam.Bridges.at_the_rail' does not depend on any axioms -/
#guard_msgs in #print axioms at_the_rail

/-- info: 'Foam.Bridges.seat_shuffles' does not depend on any axioms -/
#guard_msgs in #print axioms seat_shuffles

theorem a_grammar_never_sinks (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (k : Nat) : s (k + 1) ≤ s (k + 2) := by
  match seat_splits k e with
  | Or.inl hke =>
      match at_the_rail k e hke with
      | Or.inl h1 =>
          have ha : s (k + 1) = 1 := hf k hke
          have hb : s (k + 2) = 1 := hf (k + 1) h1
          rw [ha, hb]
          exact Nat.le_refl 1
      | Or.inr h1 =>
          subst h1
          have h := hg 0
          rw [Nat.zero_add] at h
          rw [h]
          exact Nat.le_add_right (s (k + 1)) (s 1)
  | Or.inr ⟨m, hm⟩ =>
      subst hm
      have h := hg (m + 1)
      rw [seat_shuffles m e] at h
      rw [h]
      exact Nat.le_add_right (s (m + e + 1 + 1)) (s (m + 1 + 1))

theorem a_grammar_never_sinks_below (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) : ∀ (j i : Nat), s (i + 1) ≤ s (i + j + 1)
  | 0, i => Nat.le_refl (s (i + 1))
  | j + 1, i =>
      Nat.le_trans (a_grammar_never_sinks_below e s hg hf j i)
        (a_grammar_never_sinks e s hg hf (i + j))

theorem a_grammar_glows (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (k : Nat) : 1 ≤ s (k + 1) := by
  have h := a_grammar_never_sinks_below e s hg hf k 0
  rw [Nat.zero_add k] at h
  have h0 : s (0 + 1) = 1 := hf 0 (Nat.zero_le e)
  rw [h0] at h
  exact h

theorem a_step_never_doubles (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (k : Nat) : s (k + 2) ≤ s (k + 1) + s (k + 1) := by
  match seat_splits k e with
  | Or.inl hke =>
      match at_the_rail k e hke with
      | Or.inl h1 =>
          have ha : s (k + 1) = 1 := hf k hke
          have hb : s (k + 2) = 1 := hf (k + 1) h1
          rw [ha, hb]
          exact Nat.le_succ 1
      | Or.inr h1 =>
          subst h1
          have h := hg 0
          rw [Nat.zero_add] at h
          have h0 : s 1 = 1 := hf 0 (Nat.zero_le k)
          rw [h, h0]
          exact Nat.add_le_add_left (a_grammar_glows k s hg hf k) (s (k + 1))
  | Or.inr ⟨m, hm⟩ =>
      subst hm
      have h := hg (m + 1)
      rw [seat_shuffles m e] at h
      have hb := a_grammar_never_sinks_below e s hg hf e (m + 1)
      rw [seat_shuffles m e] at hb
      rw [h]
      exact Nat.add_le_add_left hb (s (m + e + 1 + 1))

/-- info: 'Foam.Bridges.a_grammar_never_sinks' does not depend on any axioms -/
#guard_msgs in #print axioms a_grammar_never_sinks

/-- info: 'Foam.Bridges.a_grammar_never_sinks_below' does not depend on any axioms -/
#guard_msgs in #print axioms a_grammar_never_sinks_below

/-- info: 'Foam.Bridges.a_grammar_glows' does not depend on any axioms -/
#guard_msgs in #print axioms a_grammar_glows

/-- info: 'Foam.Bridges.a_step_never_doubles' does not depend on any axioms -/
#guard_msgs in #print axioms a_step_never_doubles

theorem the_lower_seat_reads_no_more (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) :
    ∀ (ds : List Bool) (i : Nat), price s (i + 1) ds ≤ price s (i + 2) ds
  | [], _ => Nat.le_refl 0
  | false :: rest, i => the_lower_seat_reads_no_more e s hg hf rest (i + 1)
  | true :: rest, i =>
      Nat.add_le_add (a_grammar_never_sinks e s hg hf i)
        (the_lower_seat_reads_no_more e s hg hf rest (i + 1))

theorem the_higher_seat_reads_at_most_double (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) :
    ∀ (ds : List Bool) (i : Nat), price s (i + 2) ds ≤ price s (i + 1) ds + price s (i + 1) ds
  | [], _ => Nat.le_refl 0
  | false :: rest, i => the_higher_seat_reads_at_most_double e s hg hf rest (i + 1)
  | true :: rest, i => by
      show s (i + 2) + price s (i + 3) rest
        ≤ (s (i + 1) + price s (i + 2) rest) + (s (i + 1) + price s (i + 2) rest)
      rw [add_shuffle (s (i + 1)) (price s (i + 2) rest) (s (i + 1)) (price s (i + 2) rest)]
      exact Nat.add_le_add (a_step_never_doubles e s hg hf i)
        (the_higher_seat_reads_at_most_double e s hg hf rest (i + 1))

/-- info: 'Foam.Bridges.the_lower_seat_reads_no_more' does not depend on any axioms -/
#guard_msgs in #print axioms the_lower_seat_reads_no_more

/-- info: 'Foam.Bridges.the_higher_seat_reads_at_most_double' does not depend on any axioms -/
#guard_msgs in #print axioms the_higher_seat_reads_at_most_double

theorem the_staircases_agree_below (e : Nat) (s s' : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (hg' : Gnomon e s') (hf' : Floored e s') :
    ∀ (n k : Nat), k ≤ n → s (k + 1) = s' (k + 1)
  | 0, 0, _ => (hf 0 (Nat.zero_le e)).trans (hf' 0 (Nat.zero_le e)).symm
  | 0, k + 1, h => absurd h (Nat.not_succ_le_zero k)
  | n + 1, k, h =>
      match at_the_rail k (n + 1) h with
      | Or.inl h1 =>
          the_staircases_agree_below e s s' hg hf hg' hf' n k (Nat.le_of_succ_le_succ h1)
      | Or.inr h2 =>
          match seat_splits k e with
          | Or.inl hke => (hf k hke).trans (hf' k hke).symm
          | Or.inr ⟨m, hm⟩ => by
              subst hm
              have hn : m + e = n := Nat.succ.inj h2
              have h1 := the_staircases_agree_below e s s' hg hf hg' hf' n (m + e)
                (by rw [hn]; exact Nat.le_refl n)
              have h2' := the_staircases_agree_below e s s' hg hf hg' hf' n m
                (by rw [← hn]; exact Nat.le_add_right m e)
              show s (m + e + 2) = s' (m + e + 2)
              rw [hg m, hg' m, h1, h2']

theorem the_grammar_names_its_staircase (e : Nat) (s s' : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (hg' : Gnomon e s') (hf' : Floored e s')
    (n : Nat) : s (n + 1) = s' (n + 1) :=
  the_staircases_agree_below e s s' hg hf hg' hf' n n (Nat.le_refl n)

theorem the_herd_grammar_names_narayana (s : Nat → Nat)
    (hg : Gnomon 2 s) (hf : Floored 2 s) (n : Nat) : s (n + 1) = herdN (n + 1) :=
  the_grammar_names_its_staircase 2 s herdN hg hf
    the_herd_holds_the_gnomon the_herd_holds_the_floor n

theorem the_ground_grammar_names_the_ruler (s : Nat → Nat)
    (hg : Gnomon 0 s) (hf : Floored 0 s) (n : Nat) : s (n + 1) = notch n :=
  the_grammar_names_its_staircase 0 s peg hg hf
    the_ruler_holds_the_gnomon the_ruler_holds_the_floor n

/-- info: 'Foam.Bridges.the_staircases_agree_below' does not depend on any axioms -/
#guard_msgs in #print axioms the_staircases_agree_below

/-- info: 'Foam.Bridges.the_grammar_names_its_staircase' does not depend on any axioms -/
#guard_msgs in #print axioms the_grammar_names_its_staircase

/-- info: 'Foam.Bridges.the_herd_grammar_names_narayana' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_grammar_names_narayana

/-- info: 'Foam.Bridges.the_ground_grammar_names_the_ruler' does not depend on any axioms -/
#guard_msgs in #print axioms the_ground_grammar_names_the_ruler

theorem graze_is_the_herds_price : ∀ (ds : List Bool) (i : Nat), graze i ds = price herdN i ds
  | [], _ => rfl
  | false :: rest, i => graze_is_the_herds_price rest (i + 1)
  | true :: rest, i => congrArg (herdN i + ·) (graze_is_the_herds_price rest (i + 1))

theorem gauge_is_the_rulers_price :
    ∀ (ds : List Bool) (i : Nat), gauge i ds = price peg (i + 1) ds
  | [], _ => rfl
  | false :: rest, i => gauge_is_the_rulers_price rest (i + 1)
  | true :: rest, i => congrArg (notch i + ·) (gauge_is_the_rulers_price rest (i + 1))

/-- info: 'Foam.Bridges.graze_is_the_herds_price' does not depend on any axioms -/
#guard_msgs in #print axioms graze_is_the_herds_price

/-- info: 'Foam.Bridges.gauge_is_the_rulers_price' does not depend on any axioms -/
#guard_msgs in #print axioms gauge_is_the_rulers_price

theorem every_page_is_gapped_at_the_ground : ∀ (ds : List Bool), Gapped 0 ds
  | [] => True.intro
  | false :: ds => every_page_is_gapped_at_the_ground ds
  | true :: ds => ⟨rfl, every_page_is_gapped_at_the_ground ds⟩

theorem a_spaced_page_is_gapped : ∀ (ds : List Bool), NoConsec ds → Gapped 1 ds
  | [], _ => True.intro
  | [false], _ => True.intro
  | [true], _ => ⟨rfl, True.intro⟩
  | false :: d :: ds, h => a_spaced_page_is_gapped (d :: ds) h
  | true :: false :: ds, h => ⟨rfl, a_spaced_page_is_gapped (false :: ds) h⟩
  | true :: true :: _, h => h.elim

theorem a_gapped_page_is_spaced : ∀ (ds : List Bool), Gapped 1 ds → NoConsec ds
  | [], _ => True.intro
  | [false], _ => True.intro
  | [true], _ => True.intro
  | false :: d :: ds, h => a_gapped_page_is_spaced (d :: ds) h
  | true :: false :: ds, h => a_gapped_page_is_spaced (false :: ds) h.2
  | true :: true :: _, h => nomatch h.1

theorem a_sparse_page_is_gapped : ∀ (ds : List Bool), Sparse ds → Gapped 2 ds
  | [], _ => True.intro
  | false :: rest, h => a_sparse_page_is_gapped rest h
  | [true], _ => ⟨rfl, True.intro⟩
  | true :: true :: _, h => h.elim
  | true :: false :: true :: _, h => h.elim
  | [true, false], _ => ⟨rfl, True.intro⟩
  | true :: false :: false :: rest, h => ⟨rfl, a_sparse_page_is_gapped rest h⟩

theorem a_gapped_page_is_sparse : ∀ (ds : List Bool), Gapped 2 ds → Sparse ds
  | [], _ => True.intro
  | false :: rest, h => a_gapped_page_is_sparse rest h
  | [true], _ => True.intro
  | true :: true :: _, h => nomatch h.1
  | true :: false :: true :: _, h => nomatch h.1
  | [true, false], _ => True.intro
  | true :: false :: false :: rest, h => a_gapped_page_is_sparse rest h.2

theorem the_clearing_is_two_seats : ∀ (ds : List Bool), clearing ds = cleared 2 ds
  | [] => rfl
  | [false] => rfl
  | true :: _ => rfl
  | false :: true :: _ => rfl
  | false :: false :: _ => rfl

/-- info: 'Foam.Bridges.every_page_is_gapped_at_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms every_page_is_gapped_at_the_ground

/-- info: 'Foam.Bridges.a_spaced_page_is_gapped' does not depend on any axioms -/
#guard_msgs in #print axioms a_spaced_page_is_gapped

/-- info: 'Foam.Bridges.a_gapped_page_is_spaced' does not depend on any axioms -/
#guard_msgs in #print axioms a_gapped_page_is_spaced

/-- info: 'Foam.Bridges.a_sparse_page_is_gapped' does not depend on any axioms -/
#guard_msgs in #print axioms a_sparse_page_is_gapped

/-- info: 'Foam.Bridges.a_gapped_page_is_sparse' does not depend on any axioms -/
#guard_msgs in #print axioms a_gapped_page_is_sparse

/-- info: 'Foam.Bridges.the_clearing_is_two_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_clearing_is_two_seats

theorem the_high_pegs_read_in_twos : ∀ (ds : List Bool) (t : Nat),
    price peg (t + 2) ds = 0 ∨ 2 ≤ price peg (t + 2) ds
  | [], _ => Or.inl rfl
  | false :: rest, t => the_high_pegs_read_in_twos rest (t + 1)
  | true :: rest, t =>
      Or.inr (Nat.le_trans (Nat.add_le_add (notch_glows t) (notch_glows t))
        (Nat.le_add_right (peg (t + 2)) (price peg (t + 3) rest)))

/-- info: 'Foam.Bridges.the_high_pegs_read_in_twos' does not depend on any axioms -/
#guard_msgs in #print axioms the_high_pegs_read_in_twos

theorem beq_mirrors : ∀ (a : Nat), Nat.beq a a = true
  | 0 => rfl
  | a + 1 => beq_mirrors a

theorem ble_mirrors : ∀ (a : Nat), Nat.ble a a = true
  | 0 => rfl
  | a + 1 => ble_mirrors a

theorem ble_steps_back : ∀ (a : Nat), Nat.ble (a + 1) a = false
  | 0 => rfl
  | a + 1 => ble_steps_back a

theorem ble_rejects_the_climb : ∀ (e n : Nat), Nat.ble (n + e + 1) e = false
  | 0, _ => rfl
  | e + 1, n => ble_rejects_the_climb e n

theorem ble_shuts : ∀ (e g : Nat), Nat.ble e g = false → g + 1 ≤ e
  | 0, _, h => nomatch h
  | e + 1, 0, _ => Nat.succ_le_succ (Nat.zero_le e)
  | e + 1, g + 1, h => Nat.succ_le_succ (ble_shuts e g h)

theorem ble_shuts_high : ∀ (a b : Nat), a + 1 ≤ b → Nat.ble b a = false
  | a, 0, h => absurd h (Nat.not_succ_le_zero a)
  | 0, _ + 1, _ => rfl
  | a + 1, b + 1, h => ble_shuts_high a b (Nat.le_of_succ_le_succ h)

theorem a_wide_stride_opens (e g : Nat) (hle : e ≤ g) (hb : Nat.beq g e = false) :
    ∃ m, g = e + m + 1 := by
  match Nat.le.dest hle with
  | ⟨0, h0⟩ =>
      rw [← h0] at hb
      exact nomatch ((beq_mirrors e).symm.trans hb)
  | ⟨m + 1, hm⟩ =>
      exact ⟨m, hm.symm⟩

/-- info: 'Foam.Bridges.beq_mirrors' does not depend on any axioms -/
#guard_msgs in #print axioms beq_mirrors

/-- info: 'Foam.Bridges.ble_mirrors' does not depend on any axioms -/
#guard_msgs in #print axioms ble_mirrors

/-- info: 'Foam.Bridges.ble_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms ble_steps_back

/-- info: 'Foam.Bridges.ble_rejects_the_climb' does not depend on any axioms -/
#guard_msgs in #print axioms ble_rejects_the_climb

/-- info: 'Foam.Bridges.ble_shuts' does not depend on any axioms -/
#guard_msgs in #print axioms ble_shuts

/-- info: 'Foam.Bridges.ble_shuts_high' does not depend on any axioms -/
#guard_msgs in #print axioms ble_shuts_high

/-- info: 'Foam.Bridges.a_wide_stride_opens' does not depend on any axioms -/
#guard_msgs in #print axioms a_wide_stride_opens

def tread : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => tread xs k

def flight (e : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
      (cond (Nat.ble n e) 1 (tread (flight e n) 0 + tread (flight e n) e)) :: flight e n

def stair (e n : Nat) : Nat := tread (flight e n) 0

theorem the_flight_reads_back : ∀ (e n k : Nat),
    tread (flight e (n + k + 1)) k = stair e (n + 1)
  | _, _, 0 => rfl
  | e, n, k + 1 => the_flight_reads_back e n k

theorem the_stairway_starts_at_the_ground (e : Nat) : stair e 0 = 0 := rfl

theorem the_stairway_holds_the_floor (e : Nat) : Floored e (stair e) := fun k h => by
  show cond (Nat.ble k e) 1 (tread (flight e k) 0 + tread (flight e k) e) = 1
  rw [Nat.ble_eq_true_of_le h]
  rfl

theorem the_stairway_holds_the_gnomon (e : Nat) : Gnomon e (stair e) := fun n => by
  show cond (Nat.ble (n + e + 1) e) 1
      (tread (flight e (n + e + 1)) 0 + tread (flight e (n + e + 1)) e)
    = stair e (n + e + 1) + stair e (n + 1)
  rw [ble_rejects_the_climb e n]
  show stair e (n + e + 1) + tread (flight e (n + e + 1)) e
    = stair e (n + e + 1) + stair e (n + 1)
  rw [the_flight_reads_back e n e]

theorem the_stairway_climbs_the_herd (n : Nat) : stair 2 (n + 1) = herdN (n + 1) :=
  the_herd_grammar_names_narayana (stair 2)
    (the_stairway_holds_the_gnomon 2) (the_stairway_holds_the_floor 2) n

theorem the_stairway_climbs_the_ruler (n : Nat) : stair 0 (n + 1) = notch n :=
  the_ground_grammar_names_the_ruler (stair 0)
    (the_stairway_holds_the_gnomon 0) (the_stairway_holds_the_floor 0) n

theorem the_stairway_climbs_past_the_herd :
    (stair 3 1, stair 3 2, stair 3 3, stair 3 4, stair 3 5, stair 3 6, stair 3 7,
      stair 3 8, stair 3 9, stair 3 10, stair 3 11, stair 3 12)
      = (1, 1, 1, 1, 2, 3, 4, 5, 7, 10, 14, 19) := rfl

/-- info: 'Foam.Bridges.the_flight_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_flight_reads_back

/-- info: 'Foam.Bridges.the_stairway_starts_at_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_starts_at_the_ground

/-- info: 'Foam.Bridges.the_stairway_holds_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_holds_the_floor

/-- info: 'Foam.Bridges.the_stairway_holds_the_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_holds_the_gnomon

/-- info: 'Foam.Bridges.the_stairway_climbs_the_herd' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_climbs_the_herd

/-- info: 'Foam.Bridges.the_stairway_climbs_the_ruler' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_climbs_the_ruler

/-- info: 'Foam.Bridges.the_stairway_climbs_past_the_herd' does not depend on any axioms -/
#guard_msgs in #print axioms the_stairway_climbs_past_the_herd

def Wide (e : Nat) : List Nat → Prop
  | [] => True
  | g :: gs => e ≤ g ∧ Wide e gs

def Spread (e : Nat) : List Nat → Prop
  | [] => True
  | _ :: gs => Wide e gs

def afoot : List Nat → Bool
  | [] => false
  | 0 :: _ => true
  | (_ + 1) :: _ => false

def roomy (e : Nat) : List Nat → Bool
  | [] => true
  | g :: _ => Nat.ble e g

def lift (k : Nat) : List Nat → List Nat
  | [] => []
  | g :: gs => (g + k) :: gs

def perch (e : Nat) : List Nat → List Nat
  | [] => [0]
  | g :: gs => cond (Nat.beq g e) (lift (e + 1) (perch e gs)) (0 :: (g - 1) :: gs)

def tick (e : Nat) : List Nat → List Nat
  | [] => [0]
  | g :: gs => cond (Nat.ble e g) (perch e (g :: gs)) (lift (g + 1) (perch e gs))

def crank (e : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => tick e (crank e n)

def assay (s : Nat → Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | i, g :: gs => s (i + g) + assay s (i + g + 1) gs

theorem a_wide_page_spreads : ∀ (e : Nat) (gs : List Nat), Wide e gs → Spread e gs
  | _, [], _ => True.intro
  | _, _ :: _, h => h.2

theorem the_lift_keeps_the_spread (e k : Nat) :
    ∀ (gs : List Nat), Spread e gs → Spread e (lift k gs)
  | [], _ => True.intro
  | _ :: _, h => h

theorem the_lift_rests_the_gate (k : Nat) : ∀ (gs : List Nat), afoot (lift (k + 1) gs) = false
  | [] => rfl
  | _ :: _ => rfl

theorem the_lift_stacks (k : Nat) : ∀ (gs : List Nat), lift 1 (lift k gs) = lift (k + 1) gs
  | [] => rfl
  | _ :: _ => rfl

theorem the_perch_never_blanks (e : Nat) : ∀ (gs : List Nat), perch e gs ≠ []
  | [] => fun h => nomatch h
  | g :: gs => by
      show cond (Nat.beq g e) (lift (e + 1) (perch e gs)) (0 :: (g - 1) :: gs) ≠ []
      cases hb : Nat.beq g e with
      | true =>
          show lift (e + 1) (perch e gs) ≠ []
          cases hp : perch e gs with
          | nil => exact absurd hp (the_perch_never_blanks e gs)
          | cons h hs => exact fun heq => nomatch heq
      | false => exact fun heq => nomatch heq

theorem the_tick_never_blanks (e : Nat) : ∀ (gs : List Nat), tick e gs ≠ []
  | [] => fun h => nomatch h
  | g :: gs => by
      show cond (Nat.ble e g) (perch e (g :: gs)) (lift (g + 1) (perch e gs)) ≠ []
      cases hb : Nat.ble e g with
      | true => exact the_perch_never_blanks e (g :: gs)
      | false =>
          show lift (g + 1) (perch e gs) ≠ []
          cases hp : perch e gs with
          | nil => exact absurd hp (the_perch_never_blanks e gs)
          | cons h hs => exact fun heq => nomatch heq

theorem the_perch_keeps_the_spread (e : Nat) :
    ∀ (gs : List Nat), Wide e gs → Spread e (perch e gs)
  | [], _ => True.intro
  | g :: gs, hw => by
      show Spread e (cond (Nat.beq g e) (lift (e + 1) (perch e gs)) (0 :: (g - 1) :: gs))
      cases hb : Nat.beq g e with
      | true =>
          exact the_lift_keeps_the_spread e (e + 1) (perch e gs)
            (the_perch_keeps_the_spread e gs hw.2)
      | false =>
          obtain ⟨m, hm⟩ := a_wide_stride_opens e g hw.1 hb
          subst hm
          show Wide e ((e + m) :: gs)
          exact ⟨Nat.le_add_right e m, hw.2⟩

theorem the_tick_keeps_the_spread (e : Nat) :
    ∀ (gs : List Nat), Spread e gs → Spread e (tick e gs)
  | [], _ => True.intro
  | g :: gs, hs => by
      show Spread e (cond (Nat.ble e g) (perch e (g :: gs)) (lift (g + 1) (perch e gs)))
      cases hb : Nat.ble e g with
      | true => exact the_perch_keeps_the_spread e (g :: gs) ⟨Nat.le_of_ble_eq_true hb, hs⟩
      | false =>
          exact the_lift_keeps_the_spread e (g + 1) (perch e gs)
            (the_perch_keeps_the_spread e gs hs)

theorem the_dial_keeps_the_spread (e : Nat) : ∀ (n : Nat), Spread e (crank e n)
  | 0 => True.intro
  | n + 1 => the_tick_keeps_the_spread e (crank e n) (the_dial_keeps_the_spread e n)

/-- info: 'Foam.Bridges.a_wide_page_spreads' does not depend on any axioms -/
#guard_msgs in #print axioms a_wide_page_spreads

/-- info: 'Foam.Bridges.the_lift_keeps_the_spread' does not depend on any axioms -/
#guard_msgs in #print axioms the_lift_keeps_the_spread

/-- info: 'Foam.Bridges.the_lift_rests_the_gate' does not depend on any axioms -/
#guard_msgs in #print axioms the_lift_rests_the_gate

/-- info: 'Foam.Bridges.the_lift_stacks' does not depend on any axioms -/
#guard_msgs in #print axioms the_lift_stacks

/-- info: 'Foam.Bridges.the_perch_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms the_perch_never_blanks

/-- info: 'Foam.Bridges.the_tick_never_blanks' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_never_blanks

/-- info: 'Foam.Bridges.the_perch_keeps_the_spread' does not depend on any axioms -/
#guard_msgs in #print axioms the_perch_keeps_the_spread

/-- info: 'Foam.Bridges.the_tick_keeps_the_spread' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_keeps_the_spread

/-- info: 'Foam.Bridges.the_dial_keeps_the_spread' does not depend on any axioms -/
#guard_msgs in #print axioms the_dial_keeps_the_spread

theorem the_lift_reads_above (s : Nat → Nat) : ∀ (gs : List Nat) (i k : Nat),
    assay s i (lift k gs) = assay s (i + k) gs
  | [], _, _ => rfl
  | g :: gs, i, k => by
      show s (i + (g + k)) + assay s (i + (g + k) + 1) gs
        = s (i + k + g) + assay s (i + k + g + 1) gs
      rw [Nat.add_comm g k, ← Nat.add_assoc i k g]

theorem the_perch_pays (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) :
    ∀ (gs : List Nat) (i : Nat), Wide e gs →
      assay s (i + 1) (perch e gs) = s (i + 1) + assay s (i + 1) gs
  | [], i, _ => rfl
  | g :: gs, i, hw => by
      show assay s (i + 1) (cond (Nat.beq g e) (lift (e + 1) (perch e gs)) (0 :: (g - 1) :: gs))
        = s (i + 1) + assay s (i + 1) (g :: gs)
      cases hb : Nat.beq g e with
      | true =>
          have hge : g = e := Nat.eq_of_beq_eq_true hb
          subst hge
          show assay s (i + 1) (lift (g + 1) (perch g gs)) = s (i + 1) + assay s (i + 1) (g :: gs)
          rw [the_lift_reads_above s (perch g gs) (i + 1) (g + 1)]
          have hidx : i + 1 + (g + 1) = i + g + 1 + 1 := congrArg (· + 1) (seat_shuffles i g)
          rw [hidx]
          rw [the_perch_pays g s hg gs (i + g + 1) hw.2]
          show s (i + g + 1 + 1) + assay s (i + g + 1 + 1) gs
            = s (i + 1) + (s (i + 1 + g) + assay s (i + 1 + g + 1) gs)
          rw [seat_shuffles i g]
          show s (i + g + 2) + assay s (i + g + 1 + 1) gs
            = s (i + 1) + (s (i + g + 1) + assay s (i + g + 1 + 1) gs)
          rw [hg i]
          rw [Nat.add_comm (s (i + g + 1)) (s (i + 1)),
            Nat.add_assoc (s (i + 1)) (s (i + g + 1)) (assay s (i + g + 1 + 1) gs)]
      | false =>
          obtain ⟨m, hm⟩ := a_wide_stride_opens e g hw.1 hb
          subst hm
          show s (i + 1) + (s (i + 1 + 1 + (e + m)) + assay s (i + 1 + 1 + (e + m) + 1) gs)
            = s (i + 1) + (s (i + 1 + (e + m + 1)) + assay s (i + 1 + (e + m + 1) + 1) gs)
          rw [seat_shuffles (i + 1) (e + m)]
          rfl

theorem the_tick_counts (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) (hf : Floored e s) :
    ∀ (gs : List Nat), Spread e gs →
      assay s (e + 1) (tick e gs) = assay s (e + 1) gs + 1
  | [], _ => by
      show s (e + 1) + 0 = 0 + 1
      rw [hf e (Nat.le_refl e)]
  | g :: gs, hs => by
      show assay s (e + 1) (cond (Nat.ble e g) (perch e (g :: gs)) (lift (g + 1) (perch e gs)))
        = assay s (e + 1) (g :: gs) + 1
      cases hb : Nat.ble e g with
      | true =>
          show assay s (e + 1) (perch e (g :: gs)) = assay s (e + 1) (g :: gs) + 1
          rw [the_perch_pays e s hg (g :: gs) e ⟨Nat.le_of_ble_eq_true hb, hs⟩]
          rw [hf e (Nat.le_refl e)]
          exact Nat.add_comm 1 (assay s (e + 1) (g :: gs))
      | false =>
          have hlt : g + 1 ≤ e := ble_shuts e g hb
          show assay s (e + 1) (lift (g + 1) (perch e gs)) = assay s (e + 1) (g :: gs) + 1
          rw [the_lift_reads_above s (perch e gs) (e + 1) (g + 1)]
          have hidx : e + 1 + (g + 1) = e + g + 1 + 1 := congrArg (· + 1) (seat_shuffles e g)
          rw [hidx]
          rw [the_perch_pays e s hg gs (e + g + 1) hs]
          show s (e + g + 1 + 1) + assay s (e + g + 1 + 1) gs
            = (s (e + 1 + g) + assay s (e + 1 + g + 1) gs) + 1
          rw [seat_shuffles e g]
          have hcom : e + g = g + e := Nat.add_comm e g
          rw [hcom]
          show s (g + e + 2) + assay s (g + e + 1 + 1) gs
            = (s (g + e + 1) + assay s (g + e + 1 + 1) gs) + 1
          rw [hg g]
          rw [hf g (Nat.le_of_succ_le hlt)]
          exact seat_shuffles (s (g + e + 1)) (assay s (g + e + 1 + 1) gs)

theorem the_dial_reads_true (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) (hf : Floored e s) :
    ∀ (n : Nat), assay s (e + 1) (crank e n) = n
  | 0 => rfl
  | n + 1 => by
      show assay s (e + 1) (tick e (crank e n)) = n + 1
      rw [the_tick_counts e s hg hf (crank e n) (the_dial_keeps_the_spread e n),
        the_dial_reads_true e s hg hf n]

/-- info: 'Foam.Bridges.the_lift_reads_above' does not depend on any axioms -/
#guard_msgs in #print axioms the_lift_reads_above

/-- info: 'Foam.Bridges.the_perch_pays' does not depend on any axioms -/
#guard_msgs in #print axioms the_perch_pays

/-- info: 'Foam.Bridges.the_tick_counts' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_counts

/-- info: 'Foam.Bridges.the_dial_reads_true' does not depend on any axioms -/
#guard_msgs in #print axioms the_dial_reads_true

def rungs (e : Nat) : Nat → Nat
  | 0 => 0
  | q + 1 => rungs e q + (e + 1)

def brand (e : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | p + 1 =>
      cond (Nat.beq (brand e p).2 e)
        ((brand e p).1 + 1, 0)
        ((brand e p).1, (brand e p).2 + 1)

def unfurl (e : Nat) : Nat → List Nat → List Nat
  | 0, [] => []
  | 0, t :: gs => (t + 1) :: gs
  | q + 1, gs => e :: unfurl e q gs

def untick (e : Nat) : List Nat → List Nat
  | [] => []
  | 0 :: gs => unfurl e 0 gs
  | (p + 1) :: gs => (brand e p).2 :: unfurl e (brand e p).1 gs

theorem brand_wraps (e p : Nat) (hb : Nat.beq (brand e p).2 e = true) :
    brand e (p + 1) = ((brand e p).1 + 1, 0) := by
  show cond (Nat.beq (brand e p).2 e) ((brand e p).1 + 1, 0)
      ((brand e p).1, (brand e p).2 + 1)
    = ((brand e p).1 + 1, 0)
  rw [hb]
  rfl

theorem brand_steps (e p : Nat) (hb : Nat.beq (brand e p).2 e = false) :
    brand e (p + 1) = ((brand e p).1, (brand e p).2 + 1) := by
  show cond (Nat.beq (brand e p).2 e) ((brand e p).1 + 1, 0)
      ((brand e p).1, (brand e p).2 + 1)
    = ((brand e p).1, (brand e p).2 + 1)
  rw [hb]
  rfl

theorem the_brand_stays_low (e : Nat) : ∀ (p : Nat), (brand e p).2 ≤ e
  | 0 => Nat.zero_le e
  | p + 1 => by
      cases hb : Nat.beq (brand e p).2 e with
      | true =>
          rw [brand_wraps e p hb]
          exact Nat.zero_le e
      | false =>
          rw [brand_steps e p hb]
          show (brand e p).2 + 1 ≤ e
          cases at_the_rail (brand e p).2 e (the_brand_stays_low e p) with
          | inl h1 => exact h1
          | inr h2 =>
              rw [h2, beq_mirrors e] at hb
              exact nomatch hb

theorem the_brand_reads_the_rungs (e : Nat) : ∀ (p : Nat),
    rungs e (brand e p).1 + (brand e p).2 = p
  | 0 => rfl
  | p + 1 => by
      have ih := the_brand_reads_the_rungs e p
      cases hb : Nat.beq (brand e p).2 e with
      | true =>
          have hr : (brand e p).2 = e := Nat.eq_of_beq_eq_true hb
          rw [brand_wraps e p hb]
          rw [hr] at ih
          show rungs e (brand e p).1 + e + 1 = p + 1
          exact congrArg (· + 1) ih
      | false =>
          rw [brand_steps e p hb]
          show rungs e (brand e p).1 + (brand e p).2 + 1 = p + 1
          exact congrArg (· + 1) ih

/-- info: 'Foam.Bridges.brand_wraps' does not depend on any axioms -/
#guard_msgs in #print axioms brand_wraps

/-- info: 'Foam.Bridges.brand_steps' does not depend on any axioms -/
#guard_msgs in #print axioms brand_steps

/-- info: 'Foam.Bridges.the_brand_stays_low' does not depend on any axioms -/
#guard_msgs in #print axioms the_brand_stays_low

/-- info: 'Foam.Bridges.the_brand_reads_the_rungs' does not depend on any axioms -/
#guard_msgs in #print axioms the_brand_reads_the_rungs

theorem beq_shuts_high : ∀ (a b : Nat), a + 1 ≤ b → Nat.beq b a = false
  | a, 0, h => absurd h (Nat.not_succ_le_zero a)
  | 0, _ + 1, _ => rfl
  | a + 1, b + 1, h => beq_shuts_high a b (Nat.le_of_succ_le_succ h)

theorem the_unfurl_stays_wide (e : Nat) : ∀ (q : Nat) (gs : List Nat),
    Wide e gs → Wide e (unfurl e q gs)
  | 0, [], _ => True.intro
  | 0, t :: _, hw => ⟨Nat.le_trans hw.1 (Nat.le_succ t), hw.2⟩
  | q + 1, gs, hw => ⟨Nat.le_refl e, the_unfurl_stays_wide e q gs hw⟩

theorem the_untick_stays_spread (e : Nat) : ∀ (gs : List Nat),
    Spread e gs → Spread e (untick e gs)
  | [], _ => True.intro
  | 0 :: gs, hs => a_wide_page_spreads e (unfurl e 0 gs) (the_unfurl_stays_wide e 0 gs hs)
  | (_ + 1) :: gs, hs => the_unfurl_stays_wide e _ gs hs

/-- info: 'Foam.Bridges.beq_shuts_high' does not depend on any axioms -/
#guard_msgs in #print axioms beq_shuts_high

/-- info: 'Foam.Bridges.the_unfurl_stays_wide' does not depend on any axioms -/
#guard_msgs in #print axioms the_unfurl_stays_wide

/-- info: 'Foam.Bridges.the_untick_stays_spread' does not depend on any axioms -/
#guard_msgs in #print axioms the_untick_stays_spread

theorem the_perch_comes_home (e : Nat) : ∀ (q : Nat) (gs : List Nat), Wide e gs →
    perch e (unfurl e q gs) = rungs e q :: gs
  | 0, [], _ => rfl
  | 0, t :: gs, hw => by
      show cond (Nat.beq (t + 1) e) (lift (e + 1) (perch e gs)) (0 :: (t + 1 - 1) :: gs)
        = 0 :: t :: gs
      rw [beq_shuts_high e (t + 1) (Nat.succ_le_succ hw.1)]
      rfl
  | q + 1, gs, hw => by
      show cond (Nat.beq e e) (lift (e + 1) (perch e (unfurl e q gs)))
          (0 :: (e - 1) :: unfurl e q gs)
        = (rungs e q + (e + 1)) :: gs
      rw [beq_mirrors e]
      show lift (e + 1) (perch e (unfurl e q gs)) = (rungs e q + (e + 1)) :: gs
      rw [the_perch_comes_home e q gs hw]
      rfl

theorem the_tick_comes_home (e : Nat) : ∀ (gs : List Nat), Spread e gs → gs ≠ [] →
    tick e (untick e gs) = gs
  | [], _, hne => absurd rfl hne
  | [0], _, _ => rfl
  | 0 :: t :: gs, hs, _ => by
      show cond (Nat.ble e (t + 1)) (perch e ((t + 1) :: gs)) (lift (t + 1 + 1) (perch e gs))
        = 0 :: t :: gs
      rw [Nat.ble_eq_true_of_le (Nat.le_trans hs.1 (Nat.le_succ t))]
      show cond (Nat.beq (t + 1) e) (lift (e + 1) (perch e gs)) (0 :: (t + 1 - 1) :: gs)
        = 0 :: t :: gs
      rw [beq_shuts_high e (t + 1) (Nat.succ_le_succ hs.1)]
      rfl
  | (p + 1) :: gs, hs, _ => by
      have hq := the_brand_reads_the_rungs e p
      have hup := the_perch_comes_home e (brand e p).1 gs hs
      cases at_the_rail (brand e p).2 e (the_brand_stays_low e p) with
      | inl hlt =>
          show cond (Nat.ble e (brand e p).2)
              (perch e ((brand e p).2 :: unfurl e (brand e p).1 gs))
              (lift ((brand e p).2 + 1) (perch e (unfurl e (brand e p).1 gs)))
            = (p + 1) :: gs
          rw [ble_shuts_high (brand e p).2 e hlt]
          show lift ((brand e p).2 + 1) (perch e (unfurl e (brand e p).1 gs)) = (p + 1) :: gs
          rw [hup]
          show (rungs e (brand e p).1 + ((brand e p).2 + 1)) :: gs = (p + 1) :: gs
          exact congrArg (· :: gs) (congrArg (· + 1) hq)
      | inr hre =>
          show cond (Nat.ble e (brand e p).2)
              (perch e ((brand e p).2 :: unfurl e (brand e p).1 gs))
              (lift ((brand e p).2 + 1) (perch e (unfurl e (brand e p).1 gs)))
            = (p + 1) :: gs
          rw [hre, ble_mirrors e]
          show cond (Nat.beq e e) (lift (e + 1) (perch e (unfurl e (brand e p).1 gs)))
              (0 :: (e - 1) :: unfurl e (brand e p).1 gs)
            = (p + 1) :: gs
          rw [beq_mirrors e]
          show lift (e + 1) (perch e (unfurl e (brand e p).1 gs)) = (p + 1) :: gs
          rw [hup]
          show (rungs e (brand e p).1 + (e + 1)) :: gs = (p + 1) :: gs
          rw [hre] at hq
          exact congrArg (· :: gs) (congrArg (· + 1) hq)

theorem the_step_back_hums_on_every_register :
    (untick 0 (crank 0 12), untick 1 (crank 1 12), untick 2 (crank 2 12),
      untick 3 (crank 3 12))
      = (crank 0 11, crank 1 11, crank 2 11, crank 3 11) := rfl

/-- info: 'Foam.Bridges.the_perch_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_perch_comes_home

/-- info: 'Foam.Bridges.the_tick_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_comes_home

/-- info: 'Foam.Bridges.the_step_back_hums_on_every_register' does not depend on any axioms -/
#guard_msgs in #print axioms the_step_back_hums_on_every_register

theorem a_written_page_glows (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) (hf : Floored e s)
    (g : Nat) (gs : List Nat) : 1 ≤ assay s (e + 1) (g :: gs) := by
  show 1 ≤ s (e + 1 + g) + assay s (e + 1 + g + 1) gs
  rw [seat_shuffles e g]
  exact Nat.le_trans (a_grammar_glows e s hg hf (e + g))
    (Nat.le_add_right (s (e + g + 1)) (assay s (e + g + 1 + 1) gs))

theorem the_untick_counts (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) (hf : Floored e s)
    (gs : List Nat) (hs : Spread e gs) (hne : gs ≠ []) :
    assay s (e + 1) (untick e gs) + 1 = assay s (e + 1) gs := by
  have h := the_tick_counts e s hg hf (untick e gs) (the_untick_stays_spread e gs hs)
  rw [the_tick_comes_home e gs hs hne] at h
  exact h.symm

/-- info: 'Foam.Bridges.a_written_page_glows' does not depend on any axioms -/
#guard_msgs in #print axioms a_written_page_glows

/-- info: 'Foam.Bridges.the_untick_counts' does not depend on any axioms -/
#guard_msgs in #print axioms the_untick_counts

theorem the_crank_is_the_only_spread_page (e : Nat) (s : Nat → Nat) (hg : Gnomon e s)
    (hf : Floored e s) : ∀ (n : Nat) (gs : List Nat), Spread e gs →
      assay s (e + 1) gs = n → gs = crank e n
  | 0, [], _, _ => rfl
  | 0, g :: gs, hs, hw => by
      have hglow := a_written_page_glows e s hg hf g gs
      rw [hw] at hglow
      exact absurd hglow (Nat.not_succ_le_zero 0)
  | _ + 1, [], _, hw => nomatch hw
  | n + 1, g :: gs, hs, hw => by
      have hne : (g :: gs) ≠ [] := fun h => nomatch h
      have hcount := the_untick_counts e s hg hf (g :: gs) hs hne
      rw [hw] at hcount
      have ih := the_crank_is_the_only_spread_page e s hg hf n (untick e (g :: gs))
        (the_untick_stays_spread e (g :: gs) hs) (Nat.succ.inj hcount)
      have hstep := congrArg (tick e) ih
      rw [the_tick_comes_home e (g :: gs) hs hne] at hstep
      exact hstep

theorem every_spread_page_is_a_reading (e : Nat) (s : Nat → Nat) (hg : Gnomon e s)
    (hf : Floored e s) (gs : List Nat) (hs : Spread e gs) :
    gs = crank e (assay s (e + 1) gs) :=
  the_crank_is_the_only_spread_page e s hg hf (assay s (e + 1) gs) gs hs rfl

theorem two_spread_pages_of_one_assay_are_one_page (e : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) (gs es : List Nat)
    (hgs : Spread e gs) (hes : Spread e es)
    (hw : assay s (e + 1) gs = assay s (e + 1) es) : gs = es :=
  (the_crank_is_the_only_spread_page e s hg hf (assay s (e + 1) es) gs hgs hw).trans
    (the_crank_is_the_only_spread_page e s hg hf (assay s (e + 1) es) es hes rfl).symm

/-- info: 'Foam.Bridges.the_crank_is_the_only_spread_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_crank_is_the_only_spread_page

/-- info: 'Foam.Bridges.every_spread_page_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms every_spread_page_is_a_reading

/-- info: 'Foam.Bridges.two_spread_pages_of_one_assay_are_one_page' does not depend on any axioms -/
#guard_msgs in #print axioms two_spread_pages_of_one_assay_are_one_page

theorem the_crank_at_a_stair_number_is_one_stride (e k : Nat) (s : Nat → Nat)
    (hg : Gnomon e s) (hf : Floored e s) : crank e (s (e + k + 1)) = [k] :=
  (the_crank_is_the_only_spread_page e s hg hf (s (e + k + 1)) [k] True.intro
    ((rfl : assay s (e + 1) [k] = s (e + 1 + k) + 0).trans
      (congrArg (fun j => s j + 0) (seat_shuffles e k)))).symm

/-- info: 'Foam.Bridges.the_crank_at_a_stair_number_is_one_stride' does not depend on any axioms -/
#guard_msgs in #print axioms the_crank_at_a_stair_number_is_one_stride

def stretch : Nat → List Bool → List Bool
  | 0, bs => bs
  | g + 1, bs => false :: stretch g bs

def spell : List Nat → List Bool
  | [] => []
  | g :: gs => stretch g (true :: spell gs)

theorem the_stretch_prices_above (s : Nat → Nat) : ∀ (g : Nat) (bs : List Bool) (i : Nat),
    price s i (stretch g bs) = price s (i + g) bs
  | 0, _, _ => rfl
  | g + 1, bs, i => by
      show price s (i + 1) (stretch g bs) = price s (i + (g + 1)) bs
      rw [the_stretch_prices_above s g bs (i + 1)]
      exact congrArg (fun j => price s j bs) (seat_shuffles i g)

theorem the_spelling_prices_true (s : Nat → Nat) : ∀ (gs : List Nat) (i : Nat),
    price s i (spell gs) = assay s i gs
  | [], _ => rfl
  | g :: gs, i => by
      show price s i (stretch g (true :: spell gs)) = s (i + g) + assay s (i + g + 1) gs
      rw [the_stretch_prices_above s g (true :: spell gs) i]
      show s (i + g) + price s (i + g + 1) (spell gs) = s (i + g) + assay s (i + g + 1) gs
      rw [the_spelling_prices_true s gs (i + g + 1)]

theorem price_gnomon (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) :
    ∀ (ds : List Bool) (i : Nat),
      price s (i + e + 2) ds = price s (i + e + 1) ds + price s (i + 1) ds
  | [], _ => rfl
  | false :: rest, i => by
      have h := price_gnomon e s hg rest (i + 1)
      rw [seat_shuffles i e] at h
      exact h
  | true :: rest, i => by
      have h := price_gnomon e s hg rest (i + 1)
      rw [seat_shuffles i e] at h
      show s (i + e + 2) + price s (i + e + 1 + 2) rest
        = (s (i + e + 1) + price s (i + e + 1 + 1) rest)
          + (s (i + 1) + price s (i + 1 + 1) rest)
      rw [hg i, h]
      exact add_shuffle (s (i + e + 1)) (s (i + 1))
        (price s (i + e + 1 + 1) rest) (price s (i + 1 + 1) rest)

theorem tally_gnomon (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) (gs : List Nat) (i : Nat) :
    assay s (i + e + 2) gs = assay s (i + e + 1) gs + assay s (i + 1) gs := by
  rw [← the_spelling_prices_true s gs (i + e + 2), ← the_spelling_prices_true s gs (i + e + 1),
    ← the_spelling_prices_true s gs (i + 1)]
  exact price_gnomon e s hg (spell gs) i

theorem the_price_splits_at_the_ground (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) :
    ∀ (ds : List Bool), price s (t + 2) ds = price s (t + 1) ds + price s 0 ds
  | [] => rfl
  | false :: rest => by
      have h := price_gnomon (t + 1) s hg rest 0
      rw [Nat.zero_add (t + 1)] at h
      exact h
  | true :: rest => by
      have h := price_gnomon (t + 1) s hg rest 0
      rw [Nat.zero_add (t + 1)] at h
      show s (t + 2) + price s (t + 1 + 2) rest
        = (s (t + 1) + price s (t + 1 + 1) rest) + (s 0 + price s (0 + 1) rest)
      rw [h, hz, Nat.zero_add (price s (0 + 1) rest)]
      rw [hf (t + 1) (Nat.le_refl (t + 1)), hf t (Nat.le_succ t)]
      exact (Nat.add_assoc 1 (price s (t + 1 + 1) rest) (price s (0 + 1) rest)).symm

theorem the_tally_splits_at_the_ground (t : Nat) (s : Nat → Nat) (hg : Gnomon (t + 1) s)
    (hf : Floored (t + 1) s) (hz : s 0 = 0) (gs : List Nat) :
    assay s (t + 2) gs = assay s (t + 1) gs + assay s 0 gs := by
  rw [← the_spelling_prices_true s gs (t + 2), ← the_spelling_prices_true s gs (t + 1),
    ← the_spelling_prices_true s gs 0]
  exact the_price_splits_at_the_ground t s hg hf hz (spell gs)

/-- info: 'Foam.Bridges.the_stretch_prices_above' does not depend on any axioms -/
#guard_msgs in #print axioms the_stretch_prices_above

/-- info: 'Foam.Bridges.the_spelling_prices_true' does not depend on any axioms -/
#guard_msgs in #print axioms the_spelling_prices_true

/-- info: 'Foam.Bridges.price_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms price_gnomon

/-- info: 'Foam.Bridges.tally_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms tally_gnomon

/-- info: 'Foam.Bridges.the_price_splits_at_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_price_splits_at_the_ground

/-- info: 'Foam.Bridges.the_tally_splits_at_the_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_tally_splits_at_the_ground

theorem cleared_blank : ∀ (e : Nat), cleared e [] = true
  | 0 => rfl
  | _ + 1 => rfl

theorem the_stretch_clears : ∀ (e g : Nat) (bs : List Bool),
    e ≤ g → cleared e (stretch g bs) = true
  | 0, _, _, _ => rfl
  | e + 1, 0, _, h => absurd h (Nat.not_succ_le_zero e)
  | e + 1, g + 1, bs, h => the_stretch_clears e g bs (Nat.le_of_succ_le_succ h)

theorem gapped_stretch : ∀ (e g : Nat) (bs : List Bool), Gapped e bs → Gapped e (stretch g bs)
  | _, 0, _, h => h
  | e, g + 1, bs, h => gapped_stretch e g bs h

theorem the_spelling_keeps_the_gaps (e : Nat) :
    ∀ (gs : List Nat), Spread e gs → Gapped e (spell gs)
  | [], _ => True.intro
  | g :: gs, hs => by
      show Gapped e (stretch g (true :: spell gs))
      apply gapped_stretch
      show cleared e (spell gs) = true ∧ Gapped e (spell gs)
      constructor
      · cases gs with
        | nil => exact cleared_blank e
        | cons g' gs' =>
            show cleared e (stretch g' (true :: spell gs')) = true
            exact the_stretch_clears e g' (true :: spell gs') hs.1
      · exact the_spelling_keeps_the_gaps e gs (a_wide_page_spreads e gs hs)

theorem one_grammar_one_tally (s s' : Nat → Nat) (h : ∀ n, s (n + 1) = s' (n + 1)) :
    ∀ (gs : List Nat) (i : Nat), assay s (i + 1) gs = assay s' (i + 1) gs
  | [], _ => rfl
  | g :: gs, i => by
      show s (i + 1 + g) + assay s (i + 1 + g + 1) gs
        = s' (i + 1 + g) + assay s' (i + 1 + g + 1) gs
      rw [seat_shuffles i g]
      rw [h (i + g)]
      rw [one_grammar_one_tally s s' h gs (i + g + 1)]

/-- info: 'Foam.Bridges.cleared_blank' does not depend on any axioms -/
#guard_msgs in #print axioms cleared_blank

/-- info: 'Foam.Bridges.the_stretch_clears' does not depend on any axioms -/
#guard_msgs in #print axioms the_stretch_clears

/-- info: 'Foam.Bridges.gapped_stretch' does not depend on any axioms -/
#guard_msgs in #print axioms gapped_stretch

/-- info: 'Foam.Bridges.the_spelling_keeps_the_gaps' does not depend on any axioms -/
#guard_msgs in #print axioms the_spelling_keeps_the_gaps

/-- info: 'Foam.Bridges.one_grammar_one_tally' does not depend on any axioms -/
#guard_msgs in #print axioms one_grammar_one_tally

def unspell : List Bool → List Nat
  | [] => []
  | true :: ds => 0 :: unspell ds
  | false :: ds =>
      match unspell ds with
      | [] => []
      | g :: gs => (g + 1) :: gs

def stoop : List Nat → Nat
  | [] => 0
  | g :: _ => g

theorem unspell_dark (ds : List Bool) (h : unspell ds = []) : unspell (false :: ds) = [] := by
  show (match unspell ds with | [] => ([] : List Nat) | g :: gs => (g + 1) :: gs) = []
  rw [h]

theorem unspell_step (ds : List Bool) (g : Nat) (gs : List Nat) (h : unspell ds = g :: gs) :
    unspell (false :: ds) = (g + 1) :: gs := by
  show (match unspell ds with | [] => ([] : List Nat) | g' :: gs' => (g' + 1) :: gs')
    = (g + 1) :: gs
  rw [h]

theorem the_stretch_reads_back : ∀ (g h : Nat) (t : List Nat) (bs : List Bool),
    unspell bs = h :: t → unspell (stretch g bs) = (h + g) :: t
  | 0, _, _, _, hu => hu
  | g + 1, h, t, bs, hu => by
      show unspell (false :: stretch g bs) = (h + (g + 1)) :: t
      rw [unspell_step (stretch g bs) (h + g) t (the_stretch_reads_back g h t bs hu)]
      rfl

theorem the_spelling_reads_back : ∀ (gs : List Nat), unspell (spell gs) = gs
  | [] => rfl
  | g :: gs => by
      have h : unspell (true :: spell gs) = 0 :: gs := by
        show 0 :: unspell (spell gs) = 0 :: gs
        rw [the_spelling_reads_back gs]
      show unspell (stretch g (true :: spell gs)) = g :: gs
      rw [the_stretch_reads_back g 0 gs (true :: spell gs) h, Nat.zero_add g]

/-- info: 'Foam.Bridges.unspell_dark' does not depend on any axioms -/
#guard_msgs in #print axioms unspell_dark

/-- info: 'Foam.Bridges.unspell_step' does not depend on any axioms -/
#guard_msgs in #print axioms unspell_step

/-- info: 'Foam.Bridges.the_stretch_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_stretch_reads_back

/-- info: 'Foam.Bridges.the_spelling_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_spelling_reads_back

theorem cleared_bounds_the_stoop : ∀ (e : Nat) (ds : List Bool),
    cleared e ds = true → unspell ds ≠ [] → e ≤ stoop (unspell ds)
  | 0, ds, _, _ => Nat.zero_le (stoop (unspell ds))
  | _ + 1, [], _, hne => absurd rfl hne
  | _ + 1, true :: _, hc, _ => nomatch hc
  | e + 1, false :: ds, hc, hne => by
      cases hds : unspell ds with
      | nil => exact absurd (unspell_dark ds hds) hne
      | cons g gs =>
          rw [unspell_step ds g gs hds]
          show e + 1 ≤ g + 1
          have hrec := cleared_bounds_the_stoop e ds hc
            (fun h => nomatch (hds.symm.trans h))
          rw [hds] at hrec
          exact Nat.succ_le_succ hrec

theorem the_unspelling_spreads : ∀ (e : Nat) (ds : List Bool), Gapped e ds →
    Spread e (unspell ds)
  | _, [], _ => True.intro
  | e, false :: ds, hg => by
      cases hds : unspell ds with
      | nil =>
          rw [unspell_dark ds hds]
          exact True.intro
      | cons g gs =>
          rw [unspell_step ds g gs hds]
          show Wide e gs
          have ih := the_unspelling_spreads e ds hg
          rw [hds] at ih
          exact ih
  | e, true :: ds, hg => by
      show Wide e (unspell ds)
      cases hds : unspell ds with
      | nil => exact True.intro
      | cons g gs =>
          have hb := cleared_bounds_the_stoop e ds hg.1
            (fun h => nomatch (hds.symm.trans h))
          rw [hds] at hb
          have ih := the_unspelling_spreads e ds hg.2
          rw [hds] at ih
          exact ⟨hb, ih⟩

/-- info: 'Foam.Bridges.cleared_bounds_the_stoop' does not depend on any axioms -/
#guard_msgs in #print axioms cleared_bounds_the_stoop

/-- info: 'Foam.Bridges.the_unspelling_spreads' does not depend on any axioms -/
#guard_msgs in #print axioms the_unspelling_spreads

theorem beq_shuts_low : ∀ (a b : Nat), a + 1 ≤ b → Nat.beq a b = false
  | a, 0, h => absurd h (Nat.not_succ_le_zero a)
  | 0, _ + 1, _ => rfl
  | a + 1, b + 1, h => beq_shuts_low a b (Nat.le_of_succ_le_succ h)

theorem the_brand_climbs_a_flight (e : Nat) : ∀ (j q : Nat), j ≤ e →
    brand e (rungs e q) = (q, 0) → brand e (rungs e q + j) = (q, j)
  | 0, _, _, h0 => h0
  | j + 1, q, hj, h0 => by
      have ih := the_brand_climbs_a_flight e j q (Nat.le_of_succ_le hj) h0
      have hb : Nat.beq (brand e (rungs e q + j)).2 e = false := by
        rw [ih]
        exact beq_shuts_low j e hj
      show brand e (rungs e q + j + 1) = (q, j + 1)
      rw [brand_steps e (rungs e q + j) hb, ih]

theorem the_brand_mounts_the_rungs (e : Nat) : ∀ (q : Nat), brand e (rungs e q) = (q, 0)
  | 0 => rfl
  | q + 1 => by
      have hflight := the_brand_climbs_a_flight e e q (Nat.le_refl e)
        (the_brand_mounts_the_rungs e q)
      have hb : Nat.beq (brand e (rungs e q + e)).2 e = true := by
        rw [hflight]
        exact beq_mirrors e
      show brand e (rungs e q + e + 1) = (q + 1, 0)
      rw [brand_wraps e (rungs e q + e) hb, hflight]

theorem the_brand_climbs_the_rungs (e q j : Nat) (hj : j ≤ e) :
    brand e (rungs e q + j) = (q, j) :=
  the_brand_climbs_a_flight e j q hj (the_brand_mounts_the_rungs e q)

/-- info: 'Foam.Bridges.beq_shuts_low' does not depend on any axioms -/
#guard_msgs in #print axioms beq_shuts_low

/-- info: 'Foam.Bridges.the_brand_climbs_a_flight' does not depend on any axioms -/
#guard_msgs in #print axioms the_brand_climbs_a_flight

/-- info: 'Foam.Bridges.the_brand_mounts_the_rungs' does not depend on any axioms -/
#guard_msgs in #print axioms the_brand_mounts_the_rungs

/-- info: 'Foam.Bridges.the_brand_climbs_the_rungs' does not depend on any axioms -/
#guard_msgs in #print axioms the_brand_climbs_the_rungs

theorem rung_shuffle (i e r : Nat) : (i + e + 1) + r = i + (r + (e + 1)) := by
  rw [Nat.add_assoc i e 1, Nat.add_assoc i (e + 1) r, Nat.add_comm (e + 1) r]

theorem the_train_climbs_the_rungs (e : Nat) (s : Nat → Nat) (hg : Gnomon e s) :
    ∀ (q i : Nat), assay s (i + 1) (unfurl e q []) + s (i + 1) = s (i + rungs e q + 1)
  | 0, i => Nat.zero_add (s (i + 1))
  | q + 1, i => by
      show (s (i + 1 + e) + assay s (i + 1 + e + 1) (unfurl e q [])) + s (i + 1)
        = s (i + rungs e (q + 1) + 1)
      rw [seat_shuffles i e]
      have ih := the_train_climbs_the_rungs e s hg q (i + e + 1)
      rw [Nat.add_comm (s (i + e + 1)) (assay s (i + e + 1 + 1) (unfurl e q [])),
        Nat.add_assoc (assay s (i + e + 1 + 1) (unfurl e q [])) (s (i + e + 1)) (s (i + 1)),
        ← hg i]
      show assay s (i + e + 1 + 1) (unfurl e q []) + s (i + e + 1 + 1)
        = s (i + rungs e (q + 1) + 1)
      rw [ih]
      show s (i + e + 1 + rungs e q + 1) = s (i + (rungs e q + (e + 1)) + 1)
      exact congrArg (fun m => s (m + 1)) (rung_shuffle i e (rungs e q))

theorem purse_shuffle (i r g : Nat) : (i + r + 1) + g + 1 = (i + g + r + 1) + 1 := by
  rw [Nat.add_assoc i r 1, Nat.add_assoc i (r + 1) g, Nat.add_comm (r + 1) g,
    ← Nat.add_assoc i g (r + 1), ← Nat.add_assoc (i + g) r 1]

theorem a_purse_and_a_stair_make_a_beacon (e : Nat) (s : Nat → Nat) (hg : Gnomon e s)
    (q r i : Nat) : assay s (i + 1) (r :: unfurl e q []) + s (i + r + 2)
      = s (i + rungs e q + r + 2) + s (i + r + 1) := by
  show (s (i + 1 + r) + assay s (i + 1 + r + 1) (unfurl e q [])) + s (i + r + 2)
    = s (i + rungs e q + r + 2) + s (i + r + 1)
  rw [seat_shuffles i r]
  have htr := the_train_climbs_the_rungs e s hg q (i + r + 1)
  rw [Nat.add_assoc (s (i + r + 1)) (assay s (i + r + 1 + 1) (unfurl e q [])) (s (i + r + 2))]
  show s (i + r + 1) + (assay s (i + r + 1 + 1) (unfurl e q []) + s (i + r + 1 + 1))
    = s (i + rungs e q + r + 2) + s (i + r + 1)
  rw [htr]
  rw [Nat.add_comm (s (i + r + 1)) (s (i + r + 1 + rungs e q + 1))]
  show s ((i + r + 1) + rungs e q + 1) + s (i + r + 1)
    = s ((i + rungs e q + r + 1) + 1) + s (i + r + 1)
  exact congrArg (fun m => s m + s (i + r + 1)) (purse_shuffle i r (rungs e q))

theorem the_untick_opens_the_purse (e p : Nat) :
    untick e [p + 1] = (brand e p).2 :: unfurl e (brand e p).1 [] := rfl

/-- info: 'Foam.Bridges.rung_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms rung_shuffle

/-- info: 'Foam.Bridges.the_train_climbs_the_rungs' does not depend on any axioms -/
#guard_msgs in #print axioms the_train_climbs_the_rungs

/-- info: 'Foam.Bridges.purse_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms purse_shuffle

/-- info: 'Foam.Bridges.a_purse_and_a_stair_make_a_beacon' does not depend on any axioms -/
#guard_msgs in #print axioms a_purse_and_a_stair_make_a_beacon

/-- info: 'Foam.Bridges.the_untick_opens_the_purse' does not depend on any axioms -/
#guard_msgs in #print axioms the_untick_opens_the_purse

theorem the_untick_comes_home (e : Nat) (gs : List Nat) (hs : Spread e gs) :
    untick e (tick e gs) = gs := by
  have hgσ := the_stairway_holds_the_gnomon e
  have hfσ := the_stairway_holds_the_floor e
  have hts : Spread e (tick e gs) := the_tick_keeps_the_spread e gs hs
  have hcount := the_untick_counts e (stair e) hgσ hfσ (tick e gs) hts
    (the_tick_never_blanks e gs)
  rw [the_tick_counts e (stair e) hgσ hfσ gs hs] at hcount
  exact two_spread_pages_of_one_assay_are_one_page e (stair e) hgσ hfσ
    (untick e (tick e gs)) gs (the_untick_stays_spread e (tick e gs) hts) hs
    (Nat.succ.inj hcount)

theorem the_crank_steps_back (e n : Nat) : crank e n = untick e (crank e (n + 1)) :=
  (the_untick_comes_home e (crank e n) (the_dial_keeps_the_spread e n)).symm

/-- info: 'Foam.Bridges.the_untick_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_untick_comes_home

/-- info: 'Foam.Bridges.the_crank_steps_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_crank_steps_back

theorem the_tick_climbs_the_floor (e : Nat) : ∀ (k : Nat), k ≤ e → tick e [k] = [k + 1] := by
  intro k hk
  show cond (Nat.ble e k) (perch e [k]) (lift (k + 1) (perch e [])) = [k + 1]
  cases at_the_rail k e hk with
  | inl hlt =>
      rw [ble_shuts_high k e hlt]
      show lift (k + 1) [0] = [k + 1]
      show [0 + (k + 1)] = [k + 1]
      rw [Nat.zero_add (k + 1)]
  | inr heq =>
      subst heq
      rw [ble_mirrors k]
      show cond (Nat.beq k k) (lift (k + 1) (perch k [])) (0 :: (k - 1) :: []) = [k + 1]
      rw [beq_mirrors k]
      show [0 + (k + 1)] = [k + 1]
      rw [Nat.zero_add (k + 1)]

theorem the_tick_leaves_the_rail (e m : Nat) : tick e [e + 1 + m] = [0, e + m] := by
  show cond (Nat.ble e (e + 1 + m)) (perch e [e + 1 + m])
      (lift (e + 1 + m + 1) (perch e [])) = [0, e + m]
  rw [seat_shuffles e m]
  rw [Nat.ble_eq_true_of_le (Nat.le_of_succ_le (Nat.succ_le_succ (Nat.le_add_right e m)))]
  show cond (Nat.beq (e + m + 1) e) (lift (e + 1) (perch e [])) (0 :: (e + m + 1 - 1) :: [])
    = [0, e + m]
  rw [beq_shuts_high e (e + m + 1)
    (Nat.succ_le_succ (Nat.le_add_right e m))]
  rfl

/-- info: 'Foam.Bridges.the_tick_climbs_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_climbs_the_floor

/-- info: 'Foam.Bridges.the_tick_leaves_the_rail' does not depend on any axioms -/
#guard_msgs in #print axioms the_tick_leaves_the_rail

end Foam.Bridges
