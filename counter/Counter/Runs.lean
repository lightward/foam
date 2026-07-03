import Counter.Actor

namespace Foam.Counter

variable {V : Type}

def correctAt (f : Nat → V → V) (v : V) : Nat → V
  | 0 => v
  | i + 1 => f i (correctAt f v i)

def recompute (f : Nat → V → V) (v : V) (s : Nat → V) : Nat → V
  | 0 => v
  | i + 1 => f i (s i)

def update (f : Nat → V → V) (v : V) (k : Nat) (s : Nat → V) (j : Nat) : V :=
  if j = k then recompute f v s k else s j

def resolve (f : Nat → V → V) (v : V) (sched : List Nat) (s : Nat → V) : Nat → V :=
  sched.foldl (fun t i => update f v i t) s

theorem update_preserves_prefix (f : Nat → V → V) (v : V) (k : Nat) (s : Nat → V)
    (j : Nat) (h : ∀ m, m < j → s m = correctAt f v m) :
    ∀ m, m < j → update f v k s m = correctAt f v m := by
  intro m hm
  show (if m = k then recompute f v s k else s m) = correctAt f v m
  by_cases hmk : m = k
  · rw [if_pos hmk]
    subst hmk
    cases m with
    | zero => rfl
    | succ i =>
      show f i (s i) = f i (correctAt f v i)
      rw [h i (Nat.lt_trans (Nat.lt_succ_self i) hm)]
  · rw [if_neg hmk]
    exact h m hm

theorem update_extends (f : Nat → V → V) (v : V) (j : Nat) (s : Nat → V)
    (h : ∀ m, m < j → s m = correctAt f v m) :
    ∀ m, m < j + 1 → update f v j s m = correctAt f v m := by
  intro m hm
  by_cases hmj : m = j
  · show (if m = j then recompute f v s j else s m) = correctAt f v m
    rw [if_pos hmj]
    subst hmj
    cases m with
    | zero => rfl
    | succ i =>
      show f i (s i) = f i (correctAt f v i)
      rw [h i (Nat.lt_succ_self i)]
  · exact update_preserves_prefix f v j s j h m
      (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hm) hmj)

inductive Threads : List Nat → List Nat → Prop
  | nil : Threads [] []
  | skip {l₁ l₂ : List Nat} (a : Nat) : Threads l₁ l₂ → Threads l₁ (a :: l₂)
  | take {l₁ l₂ : List Nat} (a : Nat) : Threads l₁ l₂ → Threads (a :: l₁) (a :: l₂)

theorem nil_threads : ∀ l : List Nat, Threads [] l
  | [] => Threads.nil
  | a :: l => Threads.skip a (nil_threads l)

def staircase : Nat → Nat → List Nat
  | _, 0 => []
  | j, k + 1 => j :: staircase (j + 1) k

theorem converges_from (f : Nat → V → V) (v : V) :
    ∀ {stair sched : List Nat}, Threads stair sched →
      ∀ j k, stair = staircase j k →
      ∀ s : Nat → V, (∀ m, m < j → s m = correctAt f v m) →
      ∀ m, m < j + k → resolve f v sched s m = correctAt f v m := by
  intro stair sched ht
  induction ht with
  | nil =>
    intro j k heq s h m hm
    cases k with
    | zero => exact h m hm
    | succ k' =>
      exact absurd heq (Ne.symm (List.cons_ne_nil j (staircase (j + 1) k')))
  | skip a ht' ih =>
    intro j k heq s h m hm
    exact ih j k heq (update f v a s) (update_preserves_prefix f v a s j h) m hm
  | take a ht' ih =>
    intro j k heq s h m hm
    cases k with
    | zero => exact absurd heq (List.cons_ne_nil a _)
    | succ k' =>
      have heq' : a :: _ = j :: staircase (j + 1) k' := heq
      injection heq' with h1 h2
      subst h1
      have hm' : m < a + 1 + k' := by
        rw [Nat.add_right_comm a 1 k']
        exact hm
      exact ih (a + 1) k' h2 (update f v a s) (update_extends f v a s h) m hm'

theorem fair_run_converges (f : Nat → V → V) (v : V)
    (sched : List Nat) (j k : Nat) (s : Nat → V)
    (ht : Threads (staircase j k) sched)
    (h : ∀ m, m < j → s m = correctAt f v m) :
    ∀ m, m < j + k → resolve f v sched s m = correctAt f v m :=
  converges_from f v ht j k rfl s h

theorem quiescent_is_correct (f : Nat → V → V) (v : V) (s : Nat → V)
    (hq : ∀ k m, update f v k s m = s m) :
    ∀ m, s m = correctAt f v m := by
  intro m
  induction m with
  | zero =>
    have h0 := hq 0 0
    show s 0 = correctAt f v 0
    rw [show correctAt f v 0 = recompute f v s 0 from rfl, ← h0]
    show update f v 0 s 0 = recompute f v s 0
    exact if_pos rfl
  | succ i ih =>
    have h1 := hq (i + 1) (i + 1)
    have h1' : recompute f v s (i + 1) = s (i + 1) := by
      rw [← h1]
      show recompute f v s (i + 1) = (if i + 1 = i + 1 then recompute f v s (i + 1) else s (i + 1))
      rw [if_pos rfl]
    show s (i + 1) = f i (correctAt f v i)
    rw [← ih]
    exact h1'.symm

theorem schedule_is_gauge (f : Nat → V → V) (v : V)
    (sched sched' : List Nat) (s s' : Nat → V) (k : Nat)
    (ht : Threads (staircase 0 k) sched) (ht' : Threads (staircase 0 k) sched')
    (m : Nat) (hm : m < k) :
    resolve f v sched s m = resolve f v sched' s' m := by
  have hz : m < 0 + k := by rw [Nat.zero_add]; exact hm
  have h1 := fair_run_converges f v sched 0 k s ht
    (fun n hn => absurd hn (Nat.not_lt_zero n)) m hz
  have h2 := fair_run_converges f v sched' 0 k s' ht'
    (fun n hn => absurd hn (Nat.not_lt_zero n)) m hz
  rw [h1, h2]

variable {G : Type} [Mul G] [One G]

def prefixActs (acts : Nat → G) : Nat → List G
  | 0 => []
  | n + 1 => prefixActs acts n ++ [acts n]

theorem correct_is_replay (S : Seat G) (p : S.Pos) (acts : Nat → G) :
    ∀ n, correctAt (fun i q => S.act (acts i) q) p n = S.replay (prefixActs acts n) p
  | 0 => rfl
  | n + 1 => by
    show S.act (acts n) (correctAt (fun i q => S.act (acts i) q) p n)
        = S.replay (prefixActs acts n ++ [acts n]) p
    rw [correct_is_replay S p acts n,
      S.replay_resumes (prefixActs acts n) [acts n] p]
    rfl

theorem quiescence_reads_settles (S : Seat G) (p : S.Pos) (acts : Nat → G)
    (s : Nat → S.Pos)
    (hq : ∀ k m, update (fun i q => S.act (acts i) q) p k s m = s m) (n : Nat) :
    s n = p ↔ Settles S (prefixActs acts n) p := by
  rw [quiescent_is_correct _ p s hq n, correct_is_replay S p acts n]
  exact Iff.rfl

/-- info: 'Foam.Counter.update_preserves_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms update_preserves_prefix

/-- info: 'Foam.Counter.update_extends' does not depend on any axioms -/
#guard_msgs in #print axioms update_extends

/-- info: 'Foam.Counter.converges_from' does not depend on any axioms -/
#guard_msgs in #print axioms converges_from

/-- info: 'Foam.Counter.fair_run_converges' does not depend on any axioms -/
#guard_msgs in #print axioms fair_run_converges

/-- info: 'Foam.Counter.quiescent_is_correct' does not depend on any axioms -/
#guard_msgs in #print axioms quiescent_is_correct

/-- info: 'Foam.Counter.schedule_is_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms schedule_is_gauge

/-- info: 'Foam.Counter.correct_is_replay' does not depend on any axioms -/
#guard_msgs in #print axioms correct_is_replay

/-- info: 'Foam.Counter.quiescence_reads_settles' does not depend on any axioms -/
#guard_msgs in #print axioms quiescence_reads_settles

end Foam.Counter
