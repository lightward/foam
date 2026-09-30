import Face
open Room Face

namespace Rest

universe u v w u' v' w' u''

def runs {I : Type u} {O : Type v} (m : Machine I O) (r : m.S → I) (rest : m.S → Bool) : m.S → Nat → Option O
  | s, 0 => cond (rest s) (some (m.out s)) none
  | s, n + 1 => cond (rest s) (some (m.out s)) (runs m r rest (m.step s (r s)) n)

structure Runner (I : Type u) (O : Type v) where
  m : Machine.{u, v, w} I O
  steer : m.S → I
  rest : m.S → Bool

def haltingGap (I : Type u) (O : Type v) : Face :=
  ⟨Runner.{u, v, w} I O, List I × Nat, Option O, fun R p => runs R.m R.steer R.rest (park R.m R.m.s0 p.1) p.2⟩

def counting : Runner Unit Nat := ⟨tally, fun _ => (), fun s => Nat.ble 3 s⟩

def carrying : Runner Unit Nat :=
  ⟨⟨Nat × Unit, (0, ()), fun s _ => (s.1 + 1, ()), fun s => s.1⟩, fun _ => (), fun s => Nat.ble 3 s.1⟩

def replayRunner {I : Type u} {O : Type v} (R : Runner.{u, v, u} I O) : Runner.{u, v, u} I O :=
  ⟨replayer R.m, fun rec => R.steer (park R.m R.m.s0 rec), fun rec => R.rest (park R.m R.m.s0 rec)⟩

def inStepWith {I : Type u} {O : Type v} (R R' : Runner.{u, v, w} I O) (B : R.m.S → R'.m.S → Prop) : Prop :=
  ∀ s t, B s t → R.steer s = R'.steer t ∧ R.rest s = R'.rest t ∧ R.m.out s = R'.m.out t ∧ ∀ i, B (R.m.step s i) (R'.m.step t i)

def coverage (A : Type u) (beq : A → A → Bool) : Runner.{u, u, u} (Round A) (Tally A) :=
  ⟨tallyMachine A, fun _ => .tick, rested beq⟩

def plan {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (w : List I) : R.m.S := park R.m R.m.s0 w

def read {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (s : R.m.S) (fuel : Nat) : Option O :=
  runs R.m R.steer R.rest s fuel

def readable {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (s : R.m.S) : Prop :=
  ∃ fuel, ∃ o, read R s fuel = some o

theorem the_intertwiner_carries_the_run {I : Type u} {O : Type v} (m n : Machine I O) (r : m.S → I) (r' : n.S → I)
    (rest : m.S → Bool) (rest' : n.S → Bool) (h : m.S → n.S)
    (hstep : ∀ s i, n.step (h s) i = h (m.step s i)) (hsteer : ∀ s, r' (h s) = r s)
    (hrest : ∀ s, rest' (h s) = rest s) (hout : ∀ s, n.out (h s) = m.out s) :
    ∀ (k : Nat) (s : m.S), runs n r' rest' (h s) k = runs m r rest s k
  | 0, s => by
      show cond (rest' (h s)) (some (n.out (h s))) none = cond (rest s) (some (m.out s)) none
      rw [hrest, hout]
  | k + 1, s => by
      show cond (rest' (h s)) (some (n.out (h s))) (runs n r' rest' (n.step (h s) (r' (h s))) k)
        = cond (rest s) (some (m.out s)) (runs m r rest (m.step s (r s)) k)
      rw [hrest, hout, hsteer, hstep, the_intertwiner_carries_the_run m n r r' rest rest' h hstep hsteer hrest hout k]

theorem a_relation_in_step_walks_the_word {I : Type u} {O : Type v} (R R' : Runner.{u, v, w} I O)
    (B : R.m.S → R'.m.S → Prop) (hB : inStepWith R R' B) :
    ∀ (w : List I) (s : R.m.S) (t : R'.m.S), B s t → B (park R.m s w) (park R'.m t w)
  | [], _, _, h => h
  | i :: w, s, t, h => a_relation_in_step_walks_the_word R R' B hB w _ _ ((hB s t h).2.2.2 i)

theorem a_relation_in_step_carries_the_run {I : Type u} {O : Type v} (R R' : Runner.{u, v, w} I O)
    (B : R.m.S → R'.m.S → Prop) (hB : inStepWith R R' B) :
    ∀ (k : Nat) (s : R.m.S) (t : R'.m.S), B s t →
      runs R.m R.steer R.rest s k = runs R'.m R'.steer R'.rest t k
  | 0, s, t, h => by
      show cond (R.rest s) (some (R.m.out s)) none = cond (R'.rest t) (some (R'.m.out t)) none
      rw [(hB s t h).2.1, (hB s t h).2.2.1]
  | k + 1, s, t, h => by
      show cond (R.rest s) (some (R.m.out s)) (runs R.m R.steer R.rest (R.m.step s (R.steer s)) k)
        = cond (R'.rest t) (some (R'.m.out t)) (runs R'.m R'.steer R'.rest (R'.m.step t (R'.steer t)) k)
      rw [(hB s t h).2.1, (hB s t h).2.2.1, (hB s t h).1,
        a_relation_in_step_carries_the_run R R' B hB k _ _ ((hB s t h).2.2.2 (R'.steer t))]

theorem an_intertwiner_is_a_relation_in_step {I : Type u} {O : Type v} (R R' : Runner.{u, v, w} I O)
    (h : R.m.S → R'.m.S)
    (hstep : ∀ s i, R'.m.step (h s) i = h (R.m.step s i)) (hsteer : ∀ s, R'.steer (h s) = R.steer s)
    (hrest : ∀ s, R'.rest (h s) = R.rest s) (hout : ∀ s, R'.m.out (h s) = R.m.out s) :
    inStepWith R R' (fun s t => h s = t) :=
  fun s _ ht => ⟨(hsteer s).symm.trans (congrArg R'.steer ht), (hrest s).symm.trans (congrArg R'.rest ht),
    (hout s).symm.trans (congrArg R'.m.out ht), fun i => (hstep s i).symm.trans (congrArg (fun x => R'.m.step x i) ht)⟩

theorem a_still_runner_rests_where_it_stands {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O)
    (h : ∀ s, R.m.step s (R.steer s) = s) :
    ∀ (n : Nat) (s : R.m.S), runs R.m R.steer R.rest s n = cond (R.rest s) (some (R.m.out s)) none
  | 0, _ => rfl
  | n + 1, s => by
      show cond (R.rest s) (some (R.m.out s)) (runs R.m R.steer R.rest (R.m.step s (R.steer s)) n)
        = cond (R.rest s) (some (R.m.out s)) none
      rw [h s, a_still_runner_rests_where_it_stands R h n s]
      cases R.rest s <;> rfl

theorem the_last_name_unlocks {A : Type u} (beq : A → A → Bool) (hrefl : ∀ y : A, beq y y = true) (t : Tally A)
    (h : lacking beq t.visited t.counts = 1) :
    ∃ k, k ∈ t.counts ∧ enrolled beq t.visited k = false ∧ rested beq (tallyStep t (.visit k)) = true := sorry

theorem a_plan_is_read_at_the_gap {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (w : List I) (fuel : Nat) :
    read R (plan R w) fuel = (haltingGap I O).obs R (w, fuel) := rfl

theorem more_fuel_reads_no_less {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) :
    ∀ (fuel : Nat) (s : R.m.S) (o : O), read R s fuel = some o → read R s (fuel + 1) = some o
  | 0, s, o, h => by
      have h' : cond (R.rest s) (some (R.m.out s)) none = some o := h
      show cond (R.rest s) (some (R.m.out s)) (runs R.m R.steer R.rest (R.m.step s (R.steer s)) 0) = some o
      cases hr : R.rest s with
      | true => rw [hr] at h'; exact h'
      | false => rw [hr] at h'; exact nomatch h'
  | fuel + 1, s, o, h => by
      have h' : cond (R.rest s) (some (R.m.out s)) (runs R.m R.steer R.rest (R.m.step s (R.steer s)) fuel) = some o := h
      show cond (R.rest s) (some (R.m.out s)) (runs R.m R.steer R.rest (R.m.step s (R.steer s)) (fuel + 1)) = some o
      cases hr : R.rest s with
      | true => rw [hr] at h'; exact h'
      | false => rw [hr] at h'; exact more_fuel_reads_no_less R fuel (R.m.step s (R.steer s)) o h'

theorem every_runner_is_a_plan_at_the_one_face (I : Type u) (O : Type v) :
    haltingGap.{u, v, w} I O = reseat (appFace (List I × Nat) (Option O)) (fun R : Runner.{u, v, w} I O => fun p => read R (plan R p.1) p.2) := sorry

theorem an_intertwined_rebody_is_unheard_at_the_halting_gap {I : Type u} {O : Type v} (R R' : Runner.{u, v, w} I O)
    (h : R.m.S → R'.m.S) (hs0 : h R.m.s0 = R'.m.s0)
    (hstep : ∀ s i, R'.m.step (h s) i = h (R.m.step s i)) (hsteer : ∀ s, R'.steer (h s) = R.steer s)
    (hrest : ∀ s, R'.rest (h s) = R.rest s) (hout : ∀ s, R'.m.out (h s) = R.m.out s) :
    alike (haltingGap I O) R' R :=
  fun p => by
    show runs R'.m R'.steer R'.rest (park R'.m R'.m.s0 p.1) p.2 = runs R.m R.steer R.rest (park R.m R.m.s0 p.1) p.2
    rw [← hs0, the_intertwined_walks_agree R.m R'.m h hstep p.1 R.m.s0,
        the_intertwiner_carries_the_run R.m R'.m R.steer R'.steer R.rest R'.rest h hstep hsteer hrest hout]

theorem two_runners_in_step_rest_alike {I : Type u} {O : Type v} (R R' : Runner.{u, v, w} I O)
    (B : R.m.S → R'.m.S → Prop) (hB : inStepWith R R' B) (h0 : B R.m.s0 R'.m.s0) :
    alike (haltingGap I O) R R' := sorry

theorem the_coverage_rests_where_it_stands {A : Type u} (beq : A → A → Bool) (t : Tally A) (n : Nat) :
    runs (coverage A beq).m (coverage A beq).steer (coverage A beq).rest t n = cond (rested beq t) (some t) none :=
  a_still_runner_rests_where_it_stands (coverage A beq) (fun _ => rfl) n t

theorem two_still_runners_rest_alike_through_a_translation {I : Type u} {I' : Type u'} {O : Type v}
    (R : Runner.{u, v, w} I O) (R' : Runner.{u', v, w'} I' O) (f : I → List I') (h : R.m.S → R'.m.S)
    (hs0 : h R.m.s0 = R'.m.s0) (hstep : ∀ s i, park R'.m (h s) (f i) = h (R.m.step s i))
    (hstill : ∀ s, R.m.step s (R.steer s) = s) (hstill' : ∀ s, R'.m.step s (R'.steer s) = s)
    (hrest : ∀ s, R'.rest (h s) = R.rest s) (hout : ∀ s, R'.m.out (h s) = R.m.out s) (w : List I) (n : Nat) :
    (haltingGap I' O).obs R' (joinMap f w, n) = (haltingGap I O).obs R (w, n) := by
  show runs R'.m R'.steer R'.rest (park R'.m R'.m.s0 (joinMap f w)) n = runs R.m R.steer R.rest (park R.m R.m.s0 w) n
  rw [a_still_runner_rests_where_it_stands R' hstill', a_still_runner_rests_where_it_stands R hstill, ← hs0,
    a_translated_intertwiner_carries_the_walk R.m R'.m f h hstep w R.m.s0, hrest, hout]

theorem any_more_fuel_reads_the_same {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (s : R.m.S) (o : O) (f : Nat)
    (h : read R s f = some o) : ∀ k : Nat, read R s (f + k) = some o
  | 0 => h
  | k + 1 => more_fuel_reads_no_less R (f + k) s o (any_more_fuel_reads_the_same R s o f h k)

theorem the_still_plan_is_readable_iff_at_rest {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O)
    (hstill : ∀ s, R.m.step s (R.steer s) = s) (s : R.m.S) : readable R s ↔ R.rest s = true :=
  ⟨(fun ⟨fuel, o, h⟩ => by
      have h' : cond (R.rest s) (some (R.m.out s)) none = some o := (a_still_runner_rests_where_it_stands R hstill fuel s).symm.trans h
      cases hr : R.rest s with
      | true => rfl
      | false => rw [hr] at h'; exact nomatch h'),
   (fun hr => ⟨0, R.m.out s, by show cond (R.rest s) (some (R.m.out s)) none = some (R.m.out s); rw [hr]; rfl⟩)⟩

theorem the_carried_unit_is_unheard_at_rest : alike (haltingGap Unit Nat) carrying counting :=
  an_intertwined_rebody_is_unheard_at_the_halting_gap counting carrying (fun s => (s, ())) rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem the_record_rests_where_the_machine_rests {I : Type u} {O : Type v} (R : Runner.{u, v, u} I O) :
    alike (haltingGap.{u, v, u} I O) R (replayRunner R) :=
  an_intertwined_rebody_is_unheard_at_the_halting_gap (replayRunner R) R (park R.m R.m.s0) rfl
    (fun rec i => (the_park_resumes R.m rec R.m.s0 [i]).symm) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem the_rest_handshake {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (h : ∀ s, R.m.step s (R.steer s) = s)
    (n : Nat) (s : R.m.S) (R' : Runner.{u, v, w} I O) (B : R.m.S → R'.m.S → Prop) (hB : inStepWith R R' B)
    (h0 : B R.m.s0 R'.m.s0) :
    runs R.m R.steer R.rest s n = cond (R.rest s) (some (R.m.out s)) none
      ∧ alike (haltingGap I O) R R' := sorry

theorem every_reader_reads_the_same {I : Type u} {O : Type v} (R : Runner.{u, v, w} I O) (s : R.m.S) (o o' : O)
    (f f' : Nat) (h : read R s f = some o) (h' : read R s f' = some o') : o = o' :=
  Option.some.inj ((any_more_fuel_reads_the_same R s o f h f').symm.trans
    ((congrArg (read R s) (Nat.add_comm f f')).trans (any_more_fuel_reads_the_same R s o' f' h' f)))

theorem the_replay_reads_the_plan {I : Type u} {O : Type v} (R : Runner.{u, v, u} I O) (w : List I) (fuel : Nat) :
    read (replayRunner R) (plan (replayRunner R) w) fuel = read R (plan R w) fuel :=
  (the_record_rests_where_the_machine_rests R (w, fuel)).symm

end Rest
