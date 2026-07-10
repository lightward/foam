import Counter.Vacancy

namespace Foam.Counter

theorem the_clean_probe {A : Type} (g h : A) :
    Balanced (cleanProbe g h)
      ∧ (cleanProbe g h).length = 2
      ∧ ∀ ws : List (A ⊕ A), Balanced ws → ws ≠ [] →
          (cleanProbe g h).length ≤ ws.length :=
  the_clean_probe_is_minimal g h

theorem consent_is_one_cell {State : Type} (c : Beholder State)
    (s : State) (p : c.Probe) :
    transcript c.toStage s [p] = [c.obs s p] :=
  rfl

theorem unconfounded_or_nothing {State : Type} (c : Beholder State)
    (s : State) (p : c.Probe)
    (bs : List (Beholder State)) (i : Fin bs.length)
    (hstarve : (seat bs i).Probe → False) :
    transcript c.toStage s [p] = [c.obs s p]
      ∧ transcript c.toStage s [] = []
      ∧ ((Beholder.fold bs).Probe → False) :=
  unconfounded_or_not_at_all c s p bs i hstarve

theorem a_mission_is_an_opinion_with_a_first_bite {S B O : Type}
    (step : S → B → S × List O) (init : S) (b : B) (bs : List B) :
    runEmit step init (b :: bs)
      = (step init b).2 ++ runEmit step (step init b).1 bs :=
  rfl

/-- info: 'Foam.Counter.the_clean_probe' does not depend on any axioms -/
#guard_msgs in #print axioms the_clean_probe

/-- info: 'Foam.Counter.consent_is_one_cell' does not depend on any axioms -/
#guard_msgs in #print axioms consent_is_one_cell

/-- info: 'Foam.Counter.unconfounded_or_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms unconfounded_or_nothing

/-- info: 'Foam.Counter.a_mission_is_an_opinion_with_a_first_bite' does not depend on any axioms -/
#guard_msgs in #print axioms a_mission_is_an_opinion_with_a_first_bite

end Foam.Counter
