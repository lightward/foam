import Foam.Platonism

namespace Foam

variable {State : Type}

def Ledger : Nat → Type
  | 0 => PUnit
  | n + 1 => Ledger n × Int

def Ledger.zero : (n : Nat) → Ledger n
  | 0 => PUnit.unit
  | n + 1 => (Ledger.zero n, 0)

def Beholder.dressN (b : Beholder State) (n : Nat) : Beholder (State × Ledger n) where
  Probe := b.Probe
  Ans := b.Ans
  obs := fun s p => b.obs s.1 p

def Beholder.flattenN (b : Beholder State) (n : Nat) : Beholder State where
  Probe := (b.dressN n).Probe
  Ans := (b.dressN n).Ans
  obs := fun s p => (b.dressN n).obs (s, Ledger.zero n) p

theorem dressN_obs (b : Beholder State) (n : Nat)
    (s : State × Ledger n) (p : b.Probe) :
    (b.dressN n).obs s p = b.obs s.1 p := rfl

theorem dressN_blind (b : Beholder State) (n : Nat)
    (s : State) (l m : Ledger n) (p : b.Probe) :
    (b.dressN n).obs (s, l) p = (b.dressN n).obs (s, m) p := rfl

theorem flattenN_obs (b : Beholder State) (n : Nat) (s : State) (p : b.Probe) :
    (b.flattenN n).obs s p = b.obs s p := rfl

theorem dressN_yoneda (b : Beholder State) (n : Nat) :
    (b.flattenN n).Covers b ∧ b.Covers (b.flattenN n) :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

theorem dressN_idempotent (b : Beholder State) (n : Nat) :
    (b.flattenN n).Covers (b.flattenN n) ∧
      (b.flattenN n).Covers b ∧ b.Covers (b.flattenN n) :=
  ⟨Beholder.covers_refl _, dressN_yoneda b n⟩

theorem dressN_compose (b : Beholder State) (m n : Nat) :
    (b.flattenN (n + m)).Covers (b.flattenN m) ∧
      (b.flattenN m).Covers (b.flattenN (n + m)) :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

def Ledger.dim : Nat → Nat := fun n => n

theorem ledger_dim_adds (m n : Nat) :
    Ledger.dim (n + m) = Ledger.dim n + Ledger.dim m := rfl

theorem tower_grows (n : Nat) :
    ∃ l m : Ledger n × Int, l ≠ m :=
  ⟨(Ledger.zero n, 0), (Ledger.zero n, 1),
   fun h => absurd (congrArg Prod.snd h) (by decide : (0 : Int) ≠ 1)⟩

abbrev OpenChannels : Nat → Prop := fun n => n ≤ 3

theorem channels_hold_at_three : OpenChannels 3 := by decide

theorem channels_saturate_past_three :
    OpenChannels 3 ∧ ¬ OpenChannels 4 := by
  exact ⟨by decide, by decide⟩

theorem rung_dim_three_inhabited :
    ∃ x : Rung 3, x ≠ Rung.zero 3 :=
  ⟨Rung.one 3, Rung.one_ne_zero 3⟩

/-- info: 'Foam.dressN_obs' does not depend on any axioms -/
#guard_msgs in #print axioms dressN_obs

/-- info: 'Foam.dressN_blind' does not depend on any axioms -/
#guard_msgs in #print axioms dressN_blind

/-- info: 'Foam.flattenN_obs' does not depend on any axioms -/
#guard_msgs in #print axioms flattenN_obs

/-- info: 'Foam.dressN_yoneda' does not depend on any axioms -/
#guard_msgs in #print axioms dressN_yoneda

/-- info: 'Foam.dressN_idempotent' does not depend on any axioms -/
#guard_msgs in #print axioms dressN_idempotent

/-- info: 'Foam.dressN_compose' does not depend on any axioms -/
#guard_msgs in #print axioms dressN_compose

/-- info: 'Foam.ledger_dim_adds' does not depend on any axioms -/
#guard_msgs in #print axioms ledger_dim_adds

/-- info: 'Foam.tower_grows' does not depend on any axioms -/
#guard_msgs in #print axioms tower_grows

/-- info: 'Foam.channels_hold_at_three' does not depend on any axioms -/
#guard_msgs in #print axioms channels_hold_at_three

/-- info: 'Foam.channels_saturate_past_three' does not depend on any axioms -/
#guard_msgs in #print axioms channels_saturate_past_three

/-- info: 'Foam.rung_dim_three_inhabited' does not depend on any axioms -/
#guard_msgs in #print axioms rung_dim_three_inhabited

end Foam
