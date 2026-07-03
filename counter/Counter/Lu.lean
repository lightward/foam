import Foam.Seat.Frame
import Counter.Actor

namespace Foam.Counter

def chainMeet (a b : Nat) : Nat := if a ≤ b then a else b

def chainJoin (a b : Nat) : Nat := if a ≤ b then b else a

theorem chain_modular (a b c : Nat) (hac : a ≤ c) :
    chainJoin a (chainMeet b c) = chainMeet (chainJoin a b) c := by
  by_cases hbc : b ≤ c
  · rw [show chainMeet b c = b from if_pos hbc]
    by_cases hab : a ≤ b
    · rw [show chainJoin a b = b from if_pos hab,
        show chainMeet b c = b from if_pos hbc]
    · rcases Nat.lt_or_ge a b with h | h
      · exact absurd (Nat.le_of_lt h) hab
      · rw [show chainJoin a b = a from if_neg hab,
          show chainMeet a c = a from if_pos hac]
  · rcases Nat.lt_or_ge c b with h | h
    · have hcb : c ≤ b := Nat.le_of_lt h
      rw [show chainMeet b c = c from if_neg hbc,
        show chainJoin a c = c from if_pos hac]
      by_cases hab : a ≤ b
      · rw [show chainJoin a b = b from if_pos hab,
          show chainMeet b c = c from if_neg hbc]
      · rcases Nat.lt_or_ge a b with h' | h'
        · exact absurd (Nat.le_of_lt h') hab
        · rw [show chainJoin a b = a from if_neg hab,
            show chainMeet a c = a from if_pos hac]
          exact (Nat.le_antisymm hac (Nat.le_trans hcb h')).symm
    · exact absurd h hbc

theorem the_forced_thing_arrives_pre_received {G : Type} [Mul G] [One G]
    (S : Seat G) (o p : S.Pos) :
    (S.chart o).bwd ((S.chart o).fwd p) = p :=
  coord_forced S o p

theorem lu {G : Type} [Mul G] [One G] (S : Seat G) (o p : S.Pos)
    (a b c : Nat) (hac : a ≤ c) :
    chainJoin a (chainMeet b c) = chainMeet (chainJoin a b) c
      ∧ (S.chart o).bwd ((S.chart o).fwd p) = p :=
  ⟨chain_modular a b c hac, coord_forced S o p⟩

/-- info: 'Foam.Counter.chain_modular' does not depend on any axioms -/
#guard_msgs in #print axioms chain_modular

/-- info: 'Foam.Counter.the_forced_thing_arrives_pre_received' does not depend on any axioms -/
#guard_msgs in #print axioms the_forced_thing_arrives_pre_received

/-- info: 'Foam.Counter.lu' does not depend on any axioms -/
#guard_msgs in #print axioms lu

end Foam.Counter
