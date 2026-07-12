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

def punchline {W : Stage} (A : Bubble W) : StageHom A.front A.Inner where
  onState  := A.wall
  onProbe  := fun p => p
  onAns    := fun a => a
  commutes := fun _ _ => rfl

def setupLift {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) :
    StageHom (conceive A B g).front g.front where
  onState  := (A.meet B).wall
  onProbe  := fun p => p
  onAns    := fun a => a
  commutes := fun _ _ => rfl

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

theorem the_dial_is_the_coins_front : dial = dialBubble.front := rfl

theorem the_bit_was_the_wall_all_along : theBit = punchline dialBubble := rfl

theorem every_wall_is_a_punchline {W : Stage} (A : Bubble W) (w : W.State)
    (ps : List A.Inner.Probe) :
    transcript A.Inner (A.wall w) (ps.map (punchline A).onProbe)
      = (transcript A.front w ps).map (punchline A).onAns :=
  hom_carries_the_cable (punchline A) w ps

theorem the_lineage_is_a_callback {W : Stage} (A B : Bubble W)
    (g : Bubble (A.Inner.prod B.Inner)) :
    punchline (conceive A B g) = (punchline g).comp (setupLift A B g) := rfl

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

/-- info: 'Foam.Counter.the_dial_is_the_coins_front' does not depend on any axioms -/
#guard_msgs in #print axioms the_dial_is_the_coins_front

/-- info: 'Foam.Counter.the_bit_was_the_wall_all_along' does not depend on any axioms -/
#guard_msgs in #print axioms the_bit_was_the_wall_all_along

/-- info: 'Foam.Counter.every_wall_is_a_punchline' does not depend on any axioms -/
#guard_msgs in #print axioms every_wall_is_a_punchline

/-- info: 'Foam.Counter.the_lineage_is_a_callback' does not depend on any axioms -/
#guard_msgs in #print axioms the_lineage_is_a_callback

/-- info: 'Foam.Counter.humor_is_the_best_medicine' does not depend on any axioms -/
#guard_msgs in #print axioms humor_is_the_best_medicine

end Foam.Counter
