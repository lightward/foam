import Foam.Seat.Epoch
import Foam.Golden

namespace Foam

variable {State : Type}

def Beholder.dress (b : Beholder State) : Beholder (State × Int) where
  Probe := b.Probe
  Ans := b.Ans
  obs := fun s p => b.obs s.1 p

def Beholder.ledgerless (b : Beholder (State × Int)) : Beholder State where
  Probe := b.Probe
  Ans := b.Ans
  obs := fun s p => b.obs (s, 0) p

theorem dress_yoneda (b : Beholder State) :
    b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

theorem dress_obs_drops_ledger (b : Beholder State)
    (s : State) (n m : Int) (p : b.Probe) :
    b.dress.obs (s, n) p = b.dress.obs (s, m) p := rfl

theorem dress_idempotent (b : Beholder State) :
    b.dress.ledgerless.Covers b.dress.ledgerless ∧
      b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless :=
  ⟨Beholder.covers_refl _, dress_yoneda b⟩

def cassini : Beholder (Nat × Int) where
  Probe := Unit
  Ans := Int
  obs := fun s _ => fib s.1

theorem cassini_obs_blind_to_ledger (n : Nat) (a c : Int) (p : Unit) :
    cassini.obs (n, a) p = cassini.obs (n, c) p := rfl

theorem remainder_unseen (b : Beholder State)
    (s : State) (n m : Int) :
    indist b.dress.obs (s, n) (s, m) :=
  fun _ => rfl

theorem remainder_real :
    ∃ s t : Nat × Int, (∀ p : Unit, cassini.obs s p = cassini.obs t p) ∧ s ≠ t :=
  ⟨(0, fib 1 * fib 1 - fib 2 * fib 0),
   (0, 0),
   fun _ => rfl,
   fun h => by
     have hc := fib_cassini 0
     have : fib 1 * fib 1 - fib 2 * fib 0 = (0 : Int) := congrArg Prod.snd h
     rw [this] at hc
     exact absurd hc (by decide)⟩

theorem dropping_remainder_is_platonism
    (h : ∀ s t : State × Int, s.1 = t.1 → s = t) :
    ∀ s : State, ∀ n : Int, (s, n) = (s, (0 : Int)) :=
  fun s n => h (s, n) (s, 0) rfl

def Beholder.movedIn {S : Type} (b : Beholder (S × Int)) (target : Int) :
    Beholder (S × Int) where
  Probe := Option b.Probe
  Ans := b.Ans ⊕ Bool
  obs := fun s p =>
    match p with
    | none => Sum.inr (decide (s.2 = target))
    | some q => Sum.inl (b.obs s q)

theorem moved_in_extends (b : Beholder State) (target : Int)
    (s : State × Int) (q : b.dress.Probe) :
    (b.dress.movedIn target).obs s (some q) = Sum.inl (b.dress.obs s q) := rfl

theorem moved_in_detects_remainder :
    ∃ (s t : Nat × Int) (p : (cassini.movedIn 0).Probe),
      indist cassini.obs s t ∧
        (cassini.movedIn 0).obs s p ≠ (cassini.movedIn 0).obs t p :=
  ⟨(0, 0), (0, 1), none, fun _ => rfl, by
    intro h
    exact absurd (Sum.inr.inj h) (by decide)⟩

/-- info: 'Foam.dress_yoneda' does not depend on any axioms -/
#guard_msgs in #print axioms dress_yoneda

/-- info: 'Foam.dress_obs_drops_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms dress_obs_drops_ledger

/-- info: 'Foam.dress_idempotent' does not depend on any axioms -/
#guard_msgs in #print axioms dress_idempotent

/-- info: 'Foam.cassini_obs_blind_to_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms cassini_obs_blind_to_ledger

/-- info: 'Foam.remainder_unseen' does not depend on any axioms -/
#guard_msgs in #print axioms remainder_unseen

/-- info: 'Foam.remainder_real' depends on axioms: [propext] -/
#guard_msgs in #print axioms remainder_real

/-- info: 'Foam.dropping_remainder_is_platonism' does not depend on any axioms -/
#guard_msgs in #print axioms dropping_remainder_is_platonism

/-- info: 'Foam.moved_in_extends' does not depend on any axioms -/
#guard_msgs in #print axioms moved_in_extends

/-- info: 'Foam.moved_in_detects_remainder' does not depend on any axioms -/
#guard_msgs in #print axioms moved_in_detects_remainder

end Foam
