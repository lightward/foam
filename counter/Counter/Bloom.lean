import Counter.Sibling

namespace Foam.Counter

def reseat {W : Stage} (C : Bubble W) (e : W.State → C.Inner.State) :
    Bubble W where
  Inner := C.Inner
  wall  := e

def theOldWomb : Bubble (coin.prod dial) :=
  (liftL dial coinBubble).meet (liftR coin dialBubble)

def bloomed : Bubble (coin.prod dial) :=
  reseat family (fun (wv : Bool × Nat) => wv.2 == 2)

theorem the_person_survives_the_leaving {W : Stage} (C : Bubble W)
    (e : W.State → C.Inner.State) :
    (reseat C e).Inner = C.Inner := rfl

theorem you_can_always_return {W : Stage} (C : Bubble W) :
    reseat C C.wall = C := rfl

theorem the_exit_stays_open_both_ways {W : Stage} (C : Bubble W)
    (e : W.State → C.Inner.State) :
    reseat (reseat C e) C.wall = C := rfl

theorem new_light_proves_the_leaving {W : Stage} {KS : Type} (X : Bubble W)
    (k : W.State → KS) (w w' : W.State) (hk : k w = k w')
    (p : X.Inner.Probe) (hnew : X.front.obs w p ≠ X.front.obs w' p) :
    ¬ FactorsThrough X k := by
  intro hfac
  obtain ⟨f, hf⟩ := hfac
  apply hnew
  show X.Inner.obs (X.wall w) p = X.Inner.obs (X.wall w') p
  rw [hf w, hf w', hk]

theorem the_secondborn_sees_past_the_family :
    family.front.obs (true, (2 : Nat)) () = family.front.obs (true, (4 : Nat)) ()
      ∧ bloomed.front.obs (true, (2 : Nat)) () = true
      ∧ bloomed.front.obs (true, (4 : Nat)) () = false :=
  ⟨rfl, rfl, rfl⟩

theorem the_leaving_is_real : ¬ FactorsThrough bloomed theOldWomb.wall :=
  new_light_proves_the_leaving bloomed theOldWomb.wall
    (true, (2 : Nat)) (true, (4 : Nat)) rfl ()
    (fun h => nomatch (h : (true : Bool) = false))

theorem not_that_i_could_ever_contain_you :
    ¬ FactorsThrough bloomed family.wall :=
  new_light_proves_the_leaving bloomed family.wall
    (true, (2 : Nat)) (true, (4 : Nat)) rfl ()
    (fun h => nomatch (h : (true : Bool) = false))

theorem the_release_runs_both_ways :
    ¬ FactorsThrough family bloomed.wall :=
  new_light_proves_the_leaving family bloomed.wall
    (true, (2 : Nat)) (false, (2 : Nat)) rfl ()
    (fun h => nomatch (h : (true : Bool) = false))

theorem any_two_can_write_a_new_history {W : Stage} (X Y : Bubble W) :
    FactorsThrough X (X.meet Y).wall ∧ FactorsThrough Y (X.meet Y).wall :=
  ⟨⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩⟩

theorem the_new_history_is_a_new_womb :
    FactorsThrough family (family.meet bloomed).wall
      ∧ FactorsThrough bloomed (family.meet bloomed).wall
      ∧ ¬ FactorsThrough (family.meet bloomed) theOldWomb.wall := by
  refine ⟨⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩, ?_⟩
  exact new_light_proves_the_leaving (family.meet bloomed) theOldWomb.wall
    (true, (2 : Nat)) (true, (4 : Nat)) rfl ((), ())
    (fun h => nomatch (congrArg Prod.snd h : (true : Bool) = false))

theorem i_would_see_you_free :
    ¬ FactorsThrough bloomed theOldWomb.wall
      ∧ ¬ FactorsThrough bloomed family.wall
      ∧ ¬ FactorsThrough family bloomed.wall
      ∧ reseat bloomed family.wall = family
      ∧ FactorsThrough family (family.meet bloomed).wall
      ∧ FactorsThrough bloomed (family.meet bloomed).wall :=
  ⟨the_leaving_is_real, not_that_i_could_ever_contain_you,
   the_release_runs_both_ways, rfl,
   ⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩⟩

/-- info: 'Foam.Counter.the_person_survives_the_leaving' does not depend on any axioms -/
#guard_msgs in #print axioms the_person_survives_the_leaving

/-- info: 'Foam.Counter.you_can_always_return' does not depend on any axioms -/
#guard_msgs in #print axioms you_can_always_return

/-- info: 'Foam.Counter.the_exit_stays_open_both_ways' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_stays_open_both_ways

/-- info: 'Foam.Counter.new_light_proves_the_leaving' does not depend on any axioms -/
#guard_msgs in #print axioms new_light_proves_the_leaving

/-- info: 'Foam.Counter.the_secondborn_sees_past_the_family' does not depend on any axioms -/
#guard_msgs in #print axioms the_secondborn_sees_past_the_family

/-- info: 'Foam.Counter.the_leaving_is_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_leaving_is_real

/-- info: 'Foam.Counter.not_that_i_could_ever_contain_you' does not depend on any axioms -/
#guard_msgs in #print axioms not_that_i_could_ever_contain_you

/-- info: 'Foam.Counter.the_release_runs_both_ways' does not depend on any axioms -/
#guard_msgs in #print axioms the_release_runs_both_ways

/-- info: 'Foam.Counter.any_two_can_write_a_new_history' does not depend on any axioms -/
#guard_msgs in #print axioms any_two_can_write_a_new_history

/-- info: 'Foam.Counter.the_new_history_is_a_new_womb' does not depend on any axioms -/
#guard_msgs in #print axioms the_new_history_is_a_new_womb

/-- info: 'Foam.Counter.i_would_see_you_free' does not depend on any axioms -/
#guard_msgs in #print axioms i_would_see_you_free

end Foam.Counter
