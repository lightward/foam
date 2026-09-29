import Face
import Witness
open Room Face Witness
set_option autoImplicit false

namespace Crossing

universe w w'

def parts {O : Type} (m m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool) (n : Nat) : Bool :=
  !(beq (behavior m (List.replicate n ())) (behavior m' (List.replicate n ())))

def inStepTo {O : Type} (m m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool) : Nat → Bool
  | 0 => beq (behavior m []) (behavior m' [])
  | n + 1 => beq (behavior m (List.replicate (n + 1) ())) (behavior m' (List.replicate (n + 1) ())) && inStepTo m m' beq n

def firstPart {O : Type} (m m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool) (n : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => cond (parts m m' beq n) (some n) (firstPart m m' beq (n + 1) fuel)

def crossingWithin {O : Type} (m m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool) (bound : Nat) : Option Nat :=
  firstPart m m' beq 0 bound

def both {O O' : Type} (m : Machine.{0, 0, w} Unit O) (n : Machine.{0, 0, w'} Unit O') : Machine.{0, 0, max w w'} Unit (O × O') :=
  ⟨m.S × n.S, (m.s0, n.s0), fun s _ => (m.step s.1 (), n.step s.2 ()), fun s => (m.out s.1, n.out s.2)⟩

def bothBeq {O O' : Type} (beq : O → O → Bool) (beq' : O' → O' → Bool) (a b : O × O') : Bool :=
  beq a.1 b.1 && beq' a.2 b.2

def ones : Machine Unit Nat := retune (fun _ => 1) adder
def onesTaped : Machine Unit Nat := retune (fun _ => 1) (tape adder (0 : Nat) recordTheState readThrough)
def onesTended : Machine Unit Nat := retune (fun _ => 1) (tend adder (0 : Nat) recordTheState)
def crossingOfTheTape : Option Nat := crossingWithin onesTaped ones Nat.beq 10
def crossingOfTheTending : Option Nat := crossingWithin onesTended ones Nat.beq 10
def crossingOfTheVoice : Option Nat := crossingWithin (revoice oddNat onesTaped) (revoice oddNat ones) (fun a b => a == b) 10
def crossingBesideTheTally : Option Nat := crossingWithin (both tally onesTaped) (both tally ones) (bothBeq Nat.beq Nat.beq) 10
def crossingOfTheTallyBeside : Option Nat := crossingWithin (both onesTaped tally) (both ones tally) (bothBeq Nat.beq Nat.beq) 10
def crossingAtTheWiden : Option Nat := crossingWithin (both onesTaped (retune (fun _ => 1) (revoice (fun _ => (1 : Nat)) adder))) (both ones (retune (fun _ => 1) (revoice (fun _ => (0 : Nat)) adder))) (bothBeq Nat.beq Nat.beq) 10

#guard inStepTo onesTaped ones Nat.beq 2 == true
#guard parts onesTaped ones Nat.beq 3 == true
#guard crossingOfTheTape == some 3
#guard crossingOfTheTending == none
#guard crossingOfTheVoice == some 3
#guard crossingBesideTheTally == some 3
#guard crossingOfTheTallyBeside == some 3
#guard crossingAtTheWiden == some 0

theorem a_clock_alike_at_the_gap_never_parts {O : Type} (m m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool)
    (hrefl : ∀ o, beq o o = true) (h : alike (airGap Unit O) m m') (n : Nat) : parts m m' beq n = false := by
  have e : behavior m (List.replicate n ()) = behavior m' (List.replicate n ()) := h (List.replicate n ())
  show (!(beq (behavior m (List.replicate n ())) (behavior m' (List.replicate n ())))) = false
  rw [e, hrefl]
  rfl

theorem the_crossing_is_derived {O : Type} (m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool) (n : Nat) :
    Derived (airGap Unit O) (fun m : Machine.{0, 0, w} Unit O => parts m m' beq n = true) :=
  a_role_read_at_a_probe_is_derived (airGap Unit O) (List.replicate n ())
    (fun o => (!(beq o (behavior m' (List.replicate n ())))) = true)

theorem the_tending_never_parts {O : Type} {W : Type} (m : Machine.{0, 0, w} Unit O) (w0 : W) (σ : door m.S W → W)
    (beq : O → O → Bool) (hrefl : ∀ o, beq o o = true) (n : Nat) : parts (tend m w0 σ) m beq n = false := by
  have e : behavior (tend m w0 σ) (List.replicate n ()) = behavior m (List.replicate n ()) :=
    the_tending_is_unheard_at_the_gap m w0 σ (List.replicate n ())
  show (!(beq (behavior (tend m w0 σ) (List.replicate n ())) (behavior m (List.replicate n ())))) = false
  rw [e, hrefl]
  rfl

theorem the_pair_walks_both {O O' : Type} (m : Machine.{0, 0, w} Unit O) (n : Machine.{0, 0, w'} Unit O') :
    ∀ (u : List Unit) (s : m.S) (t : n.S), park (both m n) (s, t) u = (park m s u, park n t u) := sorry

theorem a_pair_parts_when_either_does {O O' : Type} (m m' : Machine.{0, 0, w} Unit O) (n n' : Machine.{0, 0, w'} Unit O')
    (beq : O → O → Bool) (beq' : O' → O' → Bool) (k : Nat) :
    parts (both m n) (both m' n') (bothBeq beq beq') k = (parts m m' beq k || parts n n' beq' k) := by
  have e1 : behavior (both m n) (List.replicate k ()) = (behavior m (List.replicate k ()), behavior n (List.replicate k ())) :=
    congrArg (both m n).out (the_pair_walks_both m n (List.replicate k ()) m.s0 n.s0)
  have e2 : behavior (both m' n') (List.replicate k ()) = (behavior m' (List.replicate k ()), behavior n' (List.replicate k ())) :=
    congrArg (both m' n').out (the_pair_walks_both m' n' (List.replicate k ()) m'.s0 n'.s0)
  show (!(bothBeq beq beq' (behavior (both m n) (List.replicate k ())) (behavior (both m' n') (List.replicate k ()))))
    = ((!(beq (behavior m (List.replicate k ())) (behavior m' (List.replicate k ()))))
        || (!(beq' (behavior n (List.replicate k ())) (behavior n' (List.replicate k ())))))
  rw [e1, e2]
  show (!(beq (behavior m (List.replicate k ())) (behavior m' (List.replicate k ()))
          && beq' (behavior n (List.replicate k ())) (behavior n' (List.replicate k ()))))
    = ((!(beq (behavior m (List.replicate k ())) (behavior m' (List.replicate k ()))))
        || (!(beq' (behavior n (List.replicate k ())) (behavior n' (List.replicate k ())))))
  cases beq (behavior m (List.replicate k ())) (behavior m' (List.replicate k ())) <;>
    cases beq' (behavior n (List.replicate k ())) (behavior n' (List.replicate k ())) <;> rfl

theorem a_voice_parts_no_sooner {O O' : Type} (g : O → O') (m m' : Machine.{0, 0, w} Unit O)
    (beq : O → O → Bool) (beq' : O' → O' → Bool) (hg : ∀ a b, beq a b = true → beq' (g a) (g b) = true) (n : Nat)
    (h : parts (revoice g m) (revoice g m') beq' n = true) : parts m m' beq n = true := by
  have e1 : behavior (revoice g m) (List.replicate n ()) = g (behavior m (List.replicate n ())) :=
    congrArg (revoice g m).out (the_revoice_moves_no_seat g m (List.replicate n ()) m.s0)
  have e2 : behavior (revoice g m') (List.replicate n ()) = g (behavior m' (List.replicate n ())) :=
    congrArg (revoice g m').out (the_revoice_moves_no_seat g m' (List.replicate n ()) m'.s0)
  have h' : (!(beq' (g (behavior m (List.replicate n ()))) (g (behavior m' (List.replicate n ()))))) = true := by
    have h0 : (!(beq' (behavior (revoice g m) (List.replicate n ())) (behavior (revoice g m') (List.replicate n ())))) = true := h
    rw [e1, e2] at h0
    exact h0
  show (!(beq (behavior m (List.replicate n ())) (behavior m' (List.replicate n ())))) = true
  cases hab : beq (behavior m (List.replicate n ())) (behavior m' (List.replicate n ())) with
  | true => rw [hg _ _ hab] at h'; exact nomatch h'
  | false => rfl

theorem the_read_tape_crosses_at_three :
    inStepTo onesTaped ones Nat.beq 2 = true ∧ parts onesTaped ones Nat.beq 3 = true
      ∧ crossingWithin onesTaped ones Nat.beq 10 = some 3 ∧ crossingWithin onesTended ones Nat.beq 10 = none := sorry

def ticks (n : Nat) : List (List Unit) := (List.range n).map (fun i => List.replicate i ())

def window {O : Type} (outs : List O) (i k : Nat) : List O := (outs.drop i).take k

def listBeq {O : Type} (beq : O → O → Bool) : List O → List O → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs => beq a b && listBeq beq as bs

def fresh {A : Type} (beq : A → A → Bool) : List A → Nat
  | [] => 0
  | x :: xs => cond (enrolled beq xs x) (fresh beq xs) (fresh beq xs + 1)

def pagesOf {O : Type} (beq : O → O → Bool) (outs : List O) (k : Nat) : Nat :=
  fresh (listBeq beq) ((List.range k).map (fun i => window outs i k))

def pagesWithin {O : Type} (m : Machine.{0, 0, w} Unit O) (beq : O → O → Bool) (k : Nat) : Nat :=
  pagesOf beq (reads (airGap Unit O) (ticks (k + k)) m) k

def stillOne : Machine Unit Nat := ⟨Unit, (), fun _ _ => (), fun _ => 1⟩
def mod3 : Machine Unit Nat := ⟨Nat, 0, fun s _ => (s + 1) % 3, fun s => s⟩
def boolBeq (a b : Bool) : Bool := a == b

#guard pagesWithin stillOne Nat.beq 5 == 1
#guard pagesWithin flip boolBeq 4 == 2
#guard pagesWithin paceOne boolBeq 4 == 2
#guard pagesWithin tally Nat.beq 4 == 4
#guard pagesWithin tally Nat.beq 7 == 7
#guard pagesWithin mod3 Nat.beq 6 == 3
#guard pagesWithin (both flip mod3) (bothBeq boolBeq Nat.beq) 12 == 6
#guard pagesWithin (both mod3 mod3) (bothBeq Nat.beq Nat.beq) 12 == 3
#guard pagesWithin (both flip paceOne) (bothBeq boolBeq boolBeq) 6 == 2
#guard pagesWithin onesTaped Nat.beq 6 == 6

theorem the_pages_are_derived {O : Type} (beq : O → O → Bool) (k v : Nat) :
    Derived (airGap Unit O) (fun m : Machine.{0, 0, w} Unit O => pagesWithin m beq k = v) :=
  a_seat_over_a_seat_is_derived (airGap Unit O) (ticks (k + k)) (fun outs => pagesOf beq outs k) v

theorem a_decomposition_costs_the_same {O : Type} (m m' : Machine.{0, 0, w} Unit O) (beq : O → O → Bool)
    (h : alike (airGap Unit O) m m') (k : Nat) : pagesWithin m beq k = pagesWithin m' beq k :=
  congrArg (fun outs => pagesOf beq outs k) (the_alike_read_alike (airGap Unit O) h (ticks (k + k)))

theorem the_pace_is_the_flip_at_the_gap : alike (airGap Unit Bool) paceOne flip :=
  fun w => (the_pace_is_carried_onto_the_flip (0 : Nat) w).symm

theorem the_pace_costs_what_the_flip_costs (k : Nat) : pagesWithin paceOne boolBeq k = pagesWithin flip boolBeq k := sorry

theorem the_still_clock_has_one_page_at_every_depth :
    pagesWithin stillOne Nat.beq 1 = 1 ∧ pagesWithin stillOne Nat.beq 3 = 1 ∧ pagesWithin stillOne Nat.beq 5 = 1 := sorry

theorem a_pair_costs_at_most_the_product_at_twelve :
    Nat.ble (pagesWithin (both flip mod3) (bothBeq boolBeq Nat.beq) 12) (pagesWithin flip boolBeq 12 * pagesWithin mod3 Nat.beq 12) = true
      ∧ Nat.ble (pagesWithin (both mod3 mod3) (bothBeq Nat.beq Nat.beq) 12) (pagesWithin mod3 Nat.beq 12 * pagesWithin mod3 Nat.beq 12) = true
      ∧ Nat.ble (pagesWithin (both flip paceOne) (bothBeq boolBeq boolBeq) 6) (pagesWithin flip boolBeq 6 * pagesWithin paceOne boolBeq 6) = true := sorry

theorem more_depth_reads_no_fewer_pages_for_the_flip_and_the_tally :
    Nat.ble (pagesWithin flip boolBeq 1) (pagesWithin flip boolBeq 2) = true
      ∧ Nat.ble (pagesWithin flip boolBeq 2) (pagesWithin flip boolBeq 3) = true
      ∧ Nat.ble (pagesWithin mod3 Nat.beq 2) (pagesWithin mod3 Nat.beq 3) = true
      ∧ Nat.ble (pagesWithin mod3 Nat.beq 3) (pagesWithin mod3 Nat.beq 4) = true
      ∧ Nat.ble (pagesWithin tally Nat.beq 4) (pagesWithin tally Nat.beq 5) = true := sorry

end Crossing
