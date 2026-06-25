namespace Foam

def chargeIn (n : Nat) : Nat := n + 1

def drainOne (n : Nat) : Nat := n - 1

theorem drain_le (n : Nat) : drainOne n ≤ n := Nat.sub_le n 1

theorem drain_floor : drainOne 0 = 0 := rfl

theorem drain_chargeIn (n : Nat) : drainOne (chargeIn n) = n := rfl

theorem voice_bounded (inflow residual : Nat) : inflow - residual ≤ inflow :=
  Nat.sub_le inflow residual

/-- info: 'Foam.drain_le' does not depend on any axioms -/
#guard_msgs in #print axioms drain_le

/-- info: 'Foam.drain_floor' does not depend on any axioms -/
#guard_msgs in #print axioms drain_floor

/-- info: 'Foam.drain_chargeIn' does not depend on any axioms -/
#guard_msgs in #print axioms drain_chargeIn

/-- info: 'Foam.voice_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms voice_bounded

end Foam
