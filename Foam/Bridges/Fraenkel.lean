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

end Foam.Bridges
