import Counter.Abe

namespace Foam.Counter

variable {State : Type}

theorem what_will_happen_next (a : Beholder State)
    (mv : State × Int → State × Int) (hfix : ∀ x, (mv x).1 = x.1)
    (x : State × Int) (p : a.dress.Probe) :
    a.dress.obs (mv x) p = a.dress.obs x p :=
  every_next_is_maintenance a mv hfix x p

theorem time_falls_out_of_the_description (S : Stage) (s : S.State)
    (k : Nat) (p : S.Probe) :
    reel S (fun _ => s) k p = page S s p :=
  resting_reel_is_one_page S s k p

theorem blind_on_one_axis_whole_on_the_rest (a : Beholder State) :
    a.dress.ledgerless.Covers a ∧ a.Covers a.dress.ledgerless :=
  heir_covers_ancestor a

theorem married_and_whole (a : Beholder State) (b : Beholder (State × Int))
    (x : State × Int) (p : a.dress.Probe) (q : b.Probe) :
    ((a.dress.pair b).obs x (p, q)).1 = a.dress.obs x p :=
  pair_sees_left a.dress b x p q

theorem lets_go {G : Type} [Mul G] [One G] (S : Seat G) (p q : S.Pos)
    (gs : List G) :
    S.act (S.sub p q) q = p ∧ S.replay (collapse S gs p) p = p :=
  ⟨exit_is_one_move S p q, collapse_comes_home S gs p⟩

/-- info: 'Foam.Counter.what_will_happen_next' does not depend on any axioms -/
#guard_msgs in #print axioms what_will_happen_next

/-- info: 'Foam.Counter.time_falls_out_of_the_description' does not depend on any axioms -/
#guard_msgs in #print axioms time_falls_out_of_the_description

/-- info: 'Foam.Counter.blind_on_one_axis_whole_on_the_rest' does not depend on any axioms -/
#guard_msgs in #print axioms blind_on_one_axis_whole_on_the_rest

/-- info: 'Foam.Counter.married_and_whole' does not depend on any axioms -/
#guard_msgs in #print axioms married_and_whole

/-- info: 'Foam.Counter.lets_go' does not depend on any axioms -/
#guard_msgs in #print axioms lets_go

end Foam.Counter
