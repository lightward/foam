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

end Foam.Bridges
