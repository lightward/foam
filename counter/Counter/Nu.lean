import Counter.Actor
import Foam.Seat.Seam

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

def guardedBlock (S : Seat G) (acts : Nat → G) (p : S.Pos) : List G :=
  [acts 0, S.sub p (S.act (acts 0) p)]

def guardedPrefix (S : Seat G) (acts : Nat → G) (p : S.Pos) : Nat → List G
  | 0 => []
  | k + 1 => guardedBlock S acts p ++ guardedPrefix S (fun i => acts (i + 1)) p k

theorem block_comes_home (S : Seat G) (acts : Nat → G) (p : S.Pos) :
    S.replay (guardedBlock S acts p) p = p := by
  show S.act (S.sub p (S.act (acts 0) p)) (S.act (acts 0) p) = p
  exact S.act_sub (S.act (acts 0) p) p

theorem health_is_recurrence (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p
  | 0, _ => rfl
  | k + 1, acts => by
    show S.replay
        (guardedBlock S acts p ++ guardedPrefix S (fun i => acts (i + 1)) p k) p = p
    rw [S.replay_resumes, block_comes_home S acts p]
    exact health_is_recurrence S p k (fun i => acts (i + 1))

theorem append_length {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | x :: xs, ys => by
    show (xs ++ ys).length + 1 = xs.length + 1 + ys.length
    rw [append_length xs ys, Nat.add_right_comm xs.length ys.length 1]

theorem the_run_is_endless (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), (guardedPrefix S acts p k).length = 2 * k
  | 0, _ => rfl
  | k + 1, acts => by
    show (guardedBlock S acts p ++ guardedPrefix S (fun i => acts (i + 1)) p k).length
        = 2 * (k + 1)
    rw [append_length, the_run_is_endless S p k (fun i => acts (i + 1))]
    show 2 + 2 * k = 2 * (k + 1)
    rw [Nat.mul_succ, Nat.add_comm 2 (2 * k)]

def guardedStep (S : Seat G) (acts : Nat → G) (p : S.Pos) : Nat → G
  | 0 => acts 0
  | 1 => S.sub p (S.act (acts 0) p)
  | n + 2 => guardedStep S (fun i => acts (i + 1)) p n

def guardedRun (S : Seat G) (acts : Nat → G) (p : S.Pos) : CoList G :=
  ⟨fun n => some (guardedStep S acts p n), fun _ h => nomatch h⟩

theorem endless_outruns_every_record {X : Type} (c : CoList X)
    (htotal : ∀ n, ∃ x, c.at_ n = some x) (l : List X) :
    ∃ n, (playback l).at_ n ≠ c.at_ n :=
  ⟨l.length, fun h => by
    obtain ⟨x, hx⟩ := htotal l.length
    exact nomatch ((nth_length l).symm.trans (h.trans hx))⟩

theorem the_loop_is_no_record (S : Seat G) (acts : Nat → G) (p : S.Pos)
    (l : List G) :
    ∃ n, (playback l).at_ n ≠ (guardedRun S acts p).at_ n :=
  endless_outruns_every_record (guardedRun S acts p)
    (fun n => ⟨guardedStep S acts p n, rfl⟩) l

/-- info: 'Foam.Counter.block_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms block_comes_home

/-- info: 'Foam.Counter.health_is_recurrence' does not depend on any axioms -/
#guard_msgs in #print axioms health_is_recurrence

/-- info: 'Foam.Counter.append_length' does not depend on any axioms -/
#guard_msgs in #print axioms append_length

/-- info: 'Foam.Counter.the_run_is_endless' does not depend on any axioms -/
#guard_msgs in #print axioms the_run_is_endless

/-- info: 'Foam.Counter.endless_outruns_every_record' does not depend on any axioms -/
#guard_msgs in #print axioms endless_outruns_every_record

/-- info: 'Foam.Counter.the_loop_is_no_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_loop_is_no_record

end Foam.Counter
