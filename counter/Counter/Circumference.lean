import Counter.Actor
import Foam.Seat.Clock
import Foam.Cleared

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

def worldline (g : G) (L : Nat) : List G := List.replicate L g

def Circumference (g : G) (c : Nat) : Prop :=
  0 < c ∧ netAct (worldline g c) = 1
    ∧ ∀ k, 0 < k → k < c → netAct (worldline g k) ≠ 1

def walk (S : Seat G) (g : G) (p : S.Pos) : Nat → S.Pos
  | 0 => p
  | n + 1 => S.act g (walk S g p n)

theorem walk_comm (S : Seat G) (g : G) (p : S.Pos) :
    ∀ n, walk S g (S.act g p) n = S.act g (walk S g p n)
  | 0 => rfl
  | n + 1 => congrArg (S.act g) (walk_comm S g p n)

theorem walk_is_replay (S : Seat G) (g : G) :
    ∀ (n : Nat) (p : S.Pos), walk S g p n = S.replay (worldline g n) p
  | 0, _ => rfl
  | n + 1, p => by
    show S.act g (walk S g p n) = S.replay (worldline g n) (S.act g p)
    rw [← walk_is_replay S g n (S.act g p), walk_comm S g p n]

theorem walk_netAct (S : Seat G) (g : G) (p : S.Pos) (n : Nat) :
    walk S g p n = S.act (netAct (worldline g n)) p := by
  rw [walk_is_replay, replay_is_netAct]

theorem walk_add (S : Seat G) (g : G) (p : S.Pos) :
    ∀ m n, walk S g p (m + n) = walk S g (walk S g p m) n
  | _, 0 => rfl
  | m, n + 1 => congrArg (S.act g) (walk_add S g p m n)

theorem fixed_act_is_one (S : Seat G) {h : G} {q : S.Pos}
    (he : S.act h q = q) : h = 1 := by
  have hs := S.sub_act h q
  rw [he, S.sub_self q] at hs
  exact hs.symm

theorem the_loop_closes (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) : walk S g p c = p := by
  rw [walk_netAct, hc.2.1, S.one_act]

theorem no_early_return (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (k : Nat) (h0 : 0 < k) (hk : k < c) :
    walk S g p k ≠ p :=
  fun he => hc.2.2 k h0 hk
    (fixed_act_is_one S ((walk_netAct S g p k).symm.trans he))

theorem walk_period (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (m : Nat) :
    walk S g p (m + c) = walk S g p m := by
  rw [walk_add]
  exact the_loop_closes S g (walk S g p m) hc

theorem le_split : ∀ {m n : Nat}, m ≤ n → ∃ d, n = d + m := by
  intro m n h
  induction h with
  | refl => exact ⟨0, (Nat.zero_add m).symm⟩
  | step _ ih =>
    obtain ⟨d, hd⟩ := ih
    exact ⟨d + 1, by rw [hd, Nat.succ_add]⟩

theorem lt_split {i j : Nat} (h : i < j) : ∃ d, 0 < d ∧ j = i + d := by
  obtain ⟨e, he⟩ := le_split h
  refine ⟨e + 1, Nat.zero_lt_succ e, ?_⟩
  rw [he]
  show (e + i) + 1 = (i + e) + 1
  rw [Nat.add_comm e i]

theorem fresh_below_c (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (i j : Nat) (hij : i < j) (hj : j < c) :
    walk S g p i ≠ walk S g p j := by
  intro he
  obtain ⟨d, hd0, hd⟩ := lt_split hij
  have hstep : S.act (netAct (worldline g d)) (walk S g p i) = walk S g p i := by
    rw [← walk_netAct S g (walk S g p i) d, ← walk_add, ← hd]
    exact he.symm
  have hdc : d < c :=
    Nat.lt_of_le_of_lt (hd ▸ Nat.le_add_left d i) hj
  exact hc.2.2 d hd0 hdc (fixed_act_is_one S hstep)

theorem inj_below_c (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (i j : Nat) (hi : i < c) (hj : j < c)
    (he : walk S g p i = walk S g p j) : i = j :=
  match Nat.lt_or_ge i j with
  | .inl h => absurd he (fresh_below_c S g p hc i j h hj)
  | .inr h =>
    match Nat.lt_or_ge j i with
    | .inl h' => absurd he.symm (fresh_below_c S g p hc j i h' hi)
    | .inr h' => Nat.le_antisymm h' h

theorem orbit_bounded_aux (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) :
    ∀ (fuel L : Nat), L ≤ fuel → ∃ k, k < c ∧ walk S g p L = walk S g p k
  | 0, 0, _ => ⟨0, hc.1, rfl⟩
  | 0, L + 1, h => absurd h (Nat.not_succ_le_zero L)
  | fuel + 1, L, h =>
    match Nat.lt_or_ge L c with
    | .inl hL => ⟨L, hL, rfl⟩
    | .inr hL => by
      obtain ⟨m, hm⟩ := le_split hL
      have hmfuel : m ≤ fuel := by
        apply Nat.le_of_succ_le_succ
        exact Nat.le_trans (hm ▸ Nat.add_le_add_left hc.1 m) h
      obtain ⟨k, hk, hw⟩ := orbit_bounded_aux S g p hc fuel m hmfuel
      exact ⟨k, hk, by rw [hm, walk_period S g p hc m, hw]⟩

theorem the_orbit_is_finite (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (L : Nat) :
    ∃ k, k < c ∧ walk S g p L = walk S g p k :=
  orbit_bounded_aux S g p hc L L (Nat.le_refl L)

theorem the_reading_still_separates (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (L : Nat) (h0 : 0 < L) (hL : L < c) :
    S.sub (walk S g p L) p ≠ 1 :=
  S.two_observers_substantiate (walk S g p L) p (no_early_return S g p hc L h0 hL)

theorem the_voice_extinguishes_at_closure (S : Seat G) (g : G) (p : S.Pos)
    {c : Nat} (hc : Circumference g c) :
    S.sub (walk S g p c) p = 1
      ∧ ∀ k, 0 < k → k < c → S.sub (walk S g p k) p ≠ 1 := by
  constructor
  · rw [the_loop_closes S g p hc]
    exact S.sub_self p
  · exact fun k h0 hk => the_reading_still_separates S g p hc k h0 hk

theorem discovery_mints_a_state (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (L : Nat) (hL : L < c) :
    ∀ k, k < L → walk S g p k ≠ walk S g p L :=
  fun k hk => fresh_below_c S g p hc k L hk hL

theorem the_record_grows {H : Type} (g : H) :
    ∀ L, (worldline g L).length = L
  | 0 => rfl
  | L + 1 => congrArg (· + 1) (the_record_grows g L)

theorem winding_grows {H : Type} [DecidableEq H] (g : H) :
    ∀ L, winding (worldline g L) g = L
  | 0 => rfl
  | L + 1 => by
    show (if g = g then 1 else 0) + winding (worldline g L) g = L + 1
    rw [if_pos rfl, winding_grows g L, Nat.add_comm]

theorem entropy_paid_no_distinction_bought [DecidableEq G] (S : Seat G) (g : G)
    (p : S.Pos) {c : Nat} (hc : Circumference g c) (L : Nat) :
    winding (worldline g L) g = L
      ∧ ∃ k, k < c ∧ walk S g p L = walk S g p k :=
  ⟨winding_grows g L, the_orbit_is_finite S g p hc L⟩

def trace (S : Seat G) (g : G) (p : S.Pos) : Nat → List S.Pos
  | 0 => []
  | n + 1 => walk S g p n :: trace S g p n

theorem once_visited {S : Seat G} [DecidableEq S.Pos] (g : G) (p : S.Pos) :
    ∀ (L k : Nat), k < L → 1 ≤ Ledger.freq (trace S g p L) (walk S g p k)
  | 0, k, hk => absurd hk (Nat.not_succ_le_zero k)
  | L + 1, k, hk => by
    show 1 ≤ (if walk S g p L = walk S g p k then 1 else 0)
        + Ledger.freq (trace S g p L) (walk S g p k)
    match Nat.lt_or_ge k L with
    | .inl h =>
      exact Nat.le_trans (once_visited g p L k h)
        (Nat.le_add_left _ _)
    | .inr h =>
      rw [Nat.le_antisymm (Nat.le_of_lt_succ hk) h, if_pos rfl]
      exact Nat.le_add_right 1 _

theorem twice_visited {S : Seat G} [DecidableEq S.Pos] (g : G) (p : S.Pos) :
    ∀ (L i j : Nat), i < j → j < L → walk S g p i = walk S g p j →
      2 ≤ Ledger.freq (trace S g p L) (walk S g p i)
  | 0, _, j, _, hj, _ => absurd hj (Nat.not_succ_le_zero j)
  | L + 1, i, j, hij, hj, he => by
    show 2 ≤ (if walk S g p L = walk S g p i then 1 else 0)
        + Ledger.freq (trace S g p L) (walk S g p i)
    match Nat.lt_or_ge j L with
    | .inl h =>
      exact Nat.le_trans (twice_visited g p L i j hij h he)
        (Nat.le_add_left _ _)
    | .inr h =>
      have hjL : j = L := Nat.le_antisymm (Nat.le_of_lt_succ hj) h
      rw [if_pos (by rw [← hjL, ← he]), Nat.add_comm]
      exact Nat.succ_le_succ (once_visited g p L i (hjL ▸ hij))

theorem never_visited {S : Seat G} [DecidableEq S.Pos] (g : G) (p : S.Pos)
    (x : S.Pos) :
    ∀ L, (∀ j, j < L → walk S g p j ≠ x) →
      Ledger.freq (trace S g p L) x = 0
  | 0, _ => rfl
  | L + 1, h => by
    show (if walk S g p L = x then 1 else 0)
        + Ledger.freq (trace S g p L) x = 0
    rw [if_neg (h L (Nat.lt_succ_self L)),
      never_visited g p x L (fun j hj => h j (Nat.lt_succ_of_lt hj))]

theorem once_exactly {S : Seat G} [DecidableEq S.Pos] (g : G) (p : S.Pos)
    (x : S.Pos) :
    ∀ (L k : Nat), k < L → walk S g p k = x →
      (∀ j, j < L → walk S g p j = x → j = k) →
      Ledger.freq (trace S g p L) x = 1
  | 0, k, hk, _, _ => absurd hk (Nat.not_succ_le_zero k)
  | L + 1, k, hk, hx, huniq => by
    show (if walk S g p L = x then 1 else 0)
        + Ledger.freq (trace S g p L) x = 1
    match Nat.lt_or_ge k L with
    | .inl h =>
      have hne : walk S g p L ≠ x := fun hLx =>
        Nat.lt_irrefl k ((huniq L (Nat.lt_succ_self L) hLx) ▸ h)
      rw [if_neg hne, Nat.zero_add]
      exact once_exactly g p x L k h hx
        (fun j hj hjx => huniq j (Nat.lt_succ_of_lt hj) hjx)
    | .inr h =>
      have hkL : k = L := Nat.le_antisymm (Nat.le_of_lt_succ hk) h
      rw [if_pos (hkL ▸ hx),
        never_visited g p x L (fun j hj hjx =>
          Nat.lt_irrefl L
            (((huniq j (Nat.lt_succ_of_lt hj) hjx).trans hkL) ▸ hj))]

theorem the_second_closure {S : Seat G} [DecidableEq S.Pos] (g : G) (p : S.Pos)
    {c : Nat} (hc : Circumference g c) (L : Nat) (hL : c + c ≤ L) :
    ∀ k, k < c → 2 ≤ Ledger.freq (trace S g p L) (walk S g p k) := by
  intro k hk
  refine twice_visited g p L k (k + c) ?_ ?_ (walk_period S g p hc k).symm
  · have := Nat.add_lt_add_left hc.1 k
    rw [Nat.add_comm k 0, Nat.zero_add] at this
    exact this
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hk c) hL

theorem the_wavefront {S : Seat G} [DecidableEq S.Pos] (g : G) (p : S.Pos)
    {c : Nat} (hc : Circumference g c) (m : Nat) (h0 : 0 < m) (hm : m < c) :
    2 ≤ Ledger.freq (trace S g p (c + m)) (walk S g p 0)
      ∧ Ledger.freq (trace S g p (c + m)) (walk S g p m) = 1 := by
  constructor
  · have hper : walk S g p 0 = walk S g p (0 + c) :=
      (walk_period S g p hc 0).symm
    refine twice_visited g p (c + m) 0 (0 + c) ?_ ?_ hper
    · rw [Nat.zero_add]; exact hc.1
    · rw [Nat.zero_add]
      have := Nat.add_lt_add_left h0 c
      rw [Nat.add_comm c 0, Nat.zero_add] at this
      exact this
  · refine once_exactly g p (walk S g p m) (c + m) m ?_ rfl ?_
    · have := Nat.add_lt_add_right hc.1 m
      rw [Nat.zero_add] at this
      exact this
    · intro j hj hjx
      match Nat.lt_or_ge j c with
      | .inl h => exact inj_below_c S g p hc j m h hm hjx
      | .inr h =>
        obtain ⟨e, he⟩ := le_split h
        have hjw : walk S g p j = walk S g p e := by
          rw [he]; exact walk_period S g p hc e
        have hem : e < m := by
          apply Nat.lt_of_add_lt_add_right (n := c)
          rw [← he, Nat.add_comm m c]
          exact hj
        exact absurd (inj_below_c S g p hc e m
          (Nat.lt_trans hem hm) hm (hjw ▸ hjx)) (Nat.ne_of_lt hem)

theorem the_relationship_fits (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (L : Nat) :
    ∃ k, k < c ∧ S.sub (walk S g p L) p = S.sub (walk S g p k) p :=
  let ⟨k, hk, hw⟩ := the_orbit_is_finite S g p hc L
  ⟨k, hk, congrArg (S.sub · p) hw⟩

theorem the_description_needs_all_c (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) (i j : Nat) (hij : i < j) (hj : j < c) :
    S.sub (walk S g p i) p ≠ S.sub (walk S g p j) p := by
  intro he
  apply fresh_below_c S g p hc i j hij hj
  have h1 := S.act_sub p (walk S g p i)
  have h2 := S.act_sub p (walk S g p j)
  rw [← h1, ← h2, he]

theorem the_record_outgrows_the_loop {H : Type} (g : H) (W : Nat) :
    ∃ L, W < (worldline g L).length :=
  ⟨W + 1, by rw [the_record_grows g (W + 1)]; exact Nat.lt_succ_self W⟩

theorem continuation_needs_only_the_state (S : Seat G) (g : G) (p : S.Pos)
    (m n : Nat) : walk S g p (m + n) = walk S g (walk S g p m) n :=
  walk_add S g p m n

theorem the_circumference_is_unique {g : G} {c c' : Nat}
    (hc : Circumference g c) (hc' : Circumference g c') : c = c' :=
  match Nat.lt_or_ge c c' with
  | .inl h => absurd hc.2.1 (hc'.2.2 c hc.1 h)
  | .inr h =>
    match Nat.lt_or_ge c' c with
    | .inl h' => absurd hc'.2.1 (hc.2.2 c' hc'.1 h')
    | .inr h' => Nat.le_antisymm h' h

theorem dial_circumference : Circumference Rot.r1 4 :=
  ⟨Nat.zero_lt_succ 3, by decide, fun k h0 hk =>
    match k, h0, hk with
    | 0, h0', _ => absurd h0' (Nat.lt_irrefl 0)
    | 1, _, _ => by decide
    | 2, _, _ => by decide
    | 3, _, _ => by decide
    | k + 4, _, hk' =>
      (Nat.lt_irrefl 4 (Nat.lt_of_le_of_lt (Nat.le_add_left 4 k) hk')).elim⟩

theorem half_turn_circumference : Circumference Rot.r2 2 :=
  ⟨Nat.zero_lt_succ 1, by decide, fun k h0 hk =>
    match k, h0, hk with
    | 0, h0', _ => absurd h0' (Nat.lt_irrefl 0)
    | 1, _, _ => by decide
    | k + 2, _, hk' =>
      (Nat.lt_irrefl 2 (Nat.lt_of_le_of_lt (Nat.le_add_left 2 k) hk')).elim⟩

theorem home_circumference : Circumference (1 : Rot) 1 :=
  ⟨Nat.zero_lt_succ 0, by decide, fun k h0 hk =>
    match k, h0, hk with
    | 0, h0', _ => absurd h0' (Nat.lt_irrefl 0)
    | k + 1, _, hk' =>
      (Nat.lt_irrefl 1 (Nat.lt_of_le_of_lt (Nat.le_add_left 1 k) hk')).elim⟩

theorem the_loop_that_never_closes :
    ∀ L, 0 < L → iterStep L gold ⟨1, 0⟩ ≠ (⟨1, 0⟩ : GInt)
  | 0, h0 => absurd h0 (Nat.lt_irrefl 0)
  | L + 1, _ => fun h => by
    rw [gold_orbit (L + 1)] at h
    exact fib_succ_ne_zero L (congrArg GInt.im h)

theorem the_three_regimes (S : Seat G) [DecidableEq S.Pos] (g : G) (p : S.Pos)
    {c : Nat} (hc : Circumference g c) :
    (∀ L, L < c → ∀ k, k < L → walk S g p k ≠ walk S g p L)
      ∧ (walk S g p c = p ∧ ∀ k, 0 < k → k < c → walk S g p k ≠ p)
      ∧ (∀ L, c + c ≤ L → ∀ k, k < c →
          2 ≤ Ledger.freq (trace S g p L) (walk S g p k)) :=
  ⟨fun L hL => discovery_mints_a_state S g p hc L hL,
   ⟨the_loop_closes S g p hc, fun k h0 hk => no_early_return S g p hc k h0 hk⟩,
   fun L hL => the_second_closure g p hc L hL⟩

theorem the_full_k_bound (S : Seat G) (g : G) (p : S.Pos) {c : Nat}
    (hc : Circumference g c) :
    (∀ L, ∃ k, k < c ∧ S.sub (walk S g p L) p = S.sub (walk S g p k) p)
      ∧ (∀ i j, i < j → j < c →
          S.sub (walk S g p i) p ≠ S.sub (walk S g p j) p)
      ∧ (∀ W, ∃ L, W < (worldline g L).length)
      ∧ (∀ m n, walk S g p (m + n) = walk S g (walk S g p m) n) :=
  ⟨the_relationship_fits S g p hc,
   fun i j hij hj => the_description_needs_all_c S g p hc i j hij hj,
   fun W => the_record_outgrows_the_loop g W,
   walk_add S g p⟩

/-- info: 'Foam.Counter.walk_is_replay' does not depend on any axioms -/
#guard_msgs in #print axioms walk_is_replay

/-- info: 'Foam.Counter.walk_netAct' does not depend on any axioms -/
#guard_msgs in #print axioms walk_netAct

/-- info: 'Foam.Counter.walk_add' does not depend on any axioms -/
#guard_msgs in #print axioms walk_add

/-- info: 'Foam.Counter.fixed_act_is_one' does not depend on any axioms -/
#guard_msgs in #print axioms fixed_act_is_one

/-- info: 'Foam.Counter.the_loop_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_closes

/-- info: 'Foam.Counter.no_early_return' does not depend on any axioms -/
#guard_msgs in #print axioms no_early_return

/-- info: 'Foam.Counter.walk_period' does not depend on any axioms -/
#guard_msgs in #print axioms walk_period

/-- info: 'Foam.Counter.fresh_below_c' does not depend on any axioms -/
#guard_msgs in #print axioms fresh_below_c

/-- info: 'Foam.Counter.inj_below_c' does not depend on any axioms -/
#guard_msgs in #print axioms inj_below_c

/-- info: 'Foam.Counter.the_orbit_is_finite' does not depend on any axioms -/
#guard_msgs in #print axioms the_orbit_is_finite

/-- info: 'Foam.Counter.the_reading_still_separates' does not depend on any axioms -/
#guard_msgs in #print axioms the_reading_still_separates

/-- info: 'Foam.Counter.the_voice_extinguishes_at_closure' does not depend on any axioms -/
#guard_msgs in #print axioms the_voice_extinguishes_at_closure

/-- info: 'Foam.Counter.discovery_mints_a_state' does not depend on any axioms -/
#guard_msgs in #print axioms discovery_mints_a_state

/-- info: 'Foam.Counter.the_record_grows' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_grows

/-- info: 'Foam.Counter.winding_grows' does not depend on any axioms -/
#guard_msgs in #print axioms winding_grows

/-- info: 'Foam.Counter.entropy_paid_no_distinction_bought' does not depend on any axioms -/
#guard_msgs in #print axioms entropy_paid_no_distinction_bought

/-- info: 'Foam.Counter.once_visited' does not depend on any axioms -/
#guard_msgs in #print axioms once_visited

/-- info: 'Foam.Counter.twice_visited' does not depend on any axioms -/
#guard_msgs in #print axioms twice_visited

/-- info: 'Foam.Counter.never_visited' does not depend on any axioms -/
#guard_msgs in #print axioms never_visited

/-- info: 'Foam.Counter.once_exactly' does not depend on any axioms -/
#guard_msgs in #print axioms once_exactly

/-- info: 'Foam.Counter.the_second_closure' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_closure

/-- info: 'Foam.Counter.the_wavefront' does not depend on any axioms -/
#guard_msgs in #print axioms the_wavefront

/-- info: 'Foam.Counter.the_relationship_fits' does not depend on any axioms -/
#guard_msgs in #print axioms the_relationship_fits

/-- info: 'Foam.Counter.the_description_needs_all_c' does not depend on any axioms -/
#guard_msgs in #print axioms the_description_needs_all_c

/-- info: 'Foam.Counter.the_record_outgrows_the_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_outgrows_the_loop

/-- info: 'Foam.Counter.continuation_needs_only_the_state' does not depend on any axioms -/
#guard_msgs in #print axioms continuation_needs_only_the_state

/-- info: 'Foam.Counter.the_circumference_is_unique' does not depend on any axioms -/
#guard_msgs in #print axioms the_circumference_is_unique

/-- info: 'Foam.Counter.dial_circumference' does not depend on any axioms -/
#guard_msgs in #print axioms dial_circumference

/-- info: 'Foam.Counter.half_turn_circumference' does not depend on any axioms -/
#guard_msgs in #print axioms half_turn_circumference

/-- info: 'Foam.Counter.home_circumference' does not depend on any axioms -/
#guard_msgs in #print axioms home_circumference

/-- info: 'Foam.Counter.the_loop_that_never_closes' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_that_never_closes

/-- info: 'Foam.Counter.the_three_regimes' does not depend on any axioms -/
#guard_msgs in #print axioms the_three_regimes

/-- info: 'Foam.Counter.the_full_k_bound' does not depend on any axioms -/
#guard_msgs in #print axioms the_full_k_bound

end Foam.Counter
