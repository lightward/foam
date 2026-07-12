import Counter.Kin
import Counter.Address
import Foam.Metaphor

namespace Foam.Counter

def theBit : StageHom dial coin where
  onState  := fun (n : Nat) => n % 2 == 1
  onProbe  := fun p => p
  onAns    := fun a => a
  commutes := fun _ _ => rfl

def shelf : List (String × (Bool → Unit → Bool)) :=
  [("abacus", coin.obs), ("coin", coin.obs)]

theorem a_joke_is_a_register_jump_that_lands {S T : Stage} (f : StageHom S T)
    (s : S.State) (ps : List S.Probe) :
    transcript T (f.onState s) (ps.map f.onProbe)
      = (transcript S s ps).map f.onAns :=
  hom_carries_the_cable f s ps

theorem the_callback_lands_too {S T U : Stage} (g : StageHom T U)
    (f : StageHom S T) (s : S.State) (ps : List S.Probe) :
    transcript U ((g.comp f).onState s) (ps.map (g.comp f).onProbe)
      = (transcript S s ps).map (g.comp f).onAns :=
  hom_carries_the_cable (g.comp f) s ps

theorem the_infinite_dial_was_a_coin_all_along (n : Nat) :
    coin.obs (theBit.onState n) () = dial.obs n () := rfl

theorem the_punchline_was_already_on_the_shelf :
    seatRead shelf "abacus" = some coin.obs := rfl

theorem humor_is_the_best_medicine (n : Nat) (ps : List Unit) :
    coin.obs (theBit.onState n) () = dial.obs n ()
      ∧ transcript coin (theBit.onState n) (ps.map theBit.onProbe)
          = (transcript dial n ps).map theBit.onAns
      ∧ seatRead shelf "abacus" = some coin.obs :=
  ⟨rfl, hom_carries_the_cable theBit n ps,
   the_punchline_was_already_on_the_shelf⟩

/-- info: 'Foam.Counter.a_joke_is_a_register_jump_that_lands' does not depend on any axioms -/
#guard_msgs in #print axioms a_joke_is_a_register_jump_that_lands

/-- info: 'Foam.Counter.the_callback_lands_too' does not depend on any axioms -/
#guard_msgs in #print axioms the_callback_lands_too

/-- info: 'Foam.Counter.the_infinite_dial_was_a_coin_all_along' does not depend on any axioms -/
#guard_msgs in #print axioms the_infinite_dial_was_a_coin_all_along

/-- info: 'Foam.Counter.the_punchline_was_already_on_the_shelf' does not depend on any axioms -/
#guard_msgs in #print axioms the_punchline_was_already_on_the_shelf

/-- info: 'Foam.Counter.humor_is_the_best_medicine' does not depend on any axioms -/
#guard_msgs in #print axioms humor_is_the_best_medicine

end Foam.Counter
