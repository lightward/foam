import Foam.Int
import Foam.Bridges.Zeckendorf

namespace Foam.Bridges

def herdN : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => herdN (n + 2) + herdN n

theorem herdN_gnomon (n : Nat) : herdN (n + 3) = herdN (n + 2) + herdN n := rfl

theorem the_herd_climbs_the_stairs :
    (herdN 3, herdN 4, herdN 5, herdN 6, herdN 7, herdN 8, herdN 9, herdN 10)
      = (1, 2, 3, 4, 6, 9, 13, 19) := rfl

def graze : Nat → List Bool → Nat
  | _, [] => 0
  | i, false :: ds => graze (i + 1) ds
  | i, true :: ds => herdN i + graze (i + 1) ds

theorem add_shuffle (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, ← Nat.add_assoc b c d, Nat.add_comm b c,
      Nat.add_assoc c b d, ← Nat.add_assoc]

theorem graze_gnomon : ∀ (ds : List Bool) (i : Nat),
    graze (i + 3) ds = graze (i + 2) ds + graze i ds
  | [], _ => rfl
  | false :: rest, i => graze_gnomon rest (i + 1)
  | true :: rest, i => by
      show herdN (i + 3) + graze ((i + 1) + 3) rest
        = (herdN (i + 2) + graze ((i + 1) + 2) rest) + (herdN i + graze (i + 1) rest)
      rw [graze_gnomon rest (i + 1), herdN_gnomon]
      exact add_shuffle (herdN (i + 2)) (herdN i)
        (graze ((i + 1) + 2) rest) (graze (i + 1) rest)

def Sparse : List Bool → Prop
  | [] => True
  | false :: rest => Sparse rest
  | [true] => True
  | true :: true :: _ => False
  | true :: false :: true :: _ => False
  | [true, false] => True
  | true :: false :: false :: rest => Sparse rest

def clearing : List Bool → Bool
  | [] => true
  | [false] => true
  | true :: _ => false
  | false :: true :: _ => false
  | false :: false :: _ => true

theorem sparse_tail : ∀ {d : Bool} {ds : List Bool}, Sparse (d :: ds) → Sparse ds
  | false, _, h => h
  | true, [], _ => True.intro
  | true, true :: _, h => h.elim
  | true, [false], _ => True.intro
  | true, false :: true :: _, h => h.elim
  | true, false :: false :: _, h => h

theorem sparse_head : ∀ {ds : List Bool}, Sparse (true :: ds) → clearing ds = true
  | [], _ => rfl
  | [false], _ => rfl
  | true :: _, h => h.elim
  | false :: true :: _, h => h.elim
  | false :: false :: _, _ => rfl

theorem herd_carry_lossless (i : Nat) (rest : List Bool) :
    graze i (true :: false :: true :: false :: rest)
      = graze i (false :: false :: false :: true :: rest) := by
  show herdN i + (herdN (i + 2) + graze (i + 4) rest)
    = herdN (i + 3) + graze (i + 4) rest
  rw [herdN_gnomon i, ← Nat.add_assoc, Nat.add_comm (herdN i) (herdN (i + 2))]

theorem herd_carry_compresses (rest : List Bool) :
    ones (true :: false :: true :: false :: rest)
      = ones (false :: false :: false :: true :: rest) + 1 := rfl

/-- info: 'Foam.Bridges.herdN_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms herdN_gnomon

/-- info: 'Foam.Bridges.the_herd_climbs_the_stairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_herd_climbs_the_stairs

/-- info: 'Foam.Bridges.add_shuffle' does not depend on any axioms -/
#guard_msgs in #print axioms add_shuffle

/-- info: 'Foam.Bridges.graze_gnomon' does not depend on any axioms -/
#guard_msgs in #print axioms graze_gnomon

/-- info: 'Foam.Bridges.sparse_tail' does not depend on any axioms -/
#guard_msgs in #print axioms sparse_tail

/-- info: 'Foam.Bridges.sparse_head' does not depend on any axioms -/
#guard_msgs in #print axioms sparse_head

/-- info: 'Foam.Bridges.herd_carry_lossless' does not depend on any axioms -/
#guard_msgs in #print axioms herd_carry_lossless

/-- info: 'Foam.Bridges.herd_carry_compresses' does not depend on any axioms -/
#guard_msgs in #print axioms herd_carry_compresses

end Foam.Bridges
