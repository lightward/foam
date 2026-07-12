import Counter.Bloom

namespace Foam.Counter

theorem blindness_cannot_read_itself {W : Stage} {R : Type} (X : Bubble W)
    (w w' : W.State) (h : X.wall w = X.wall w') (p : X.Inner.Probe)
    (d : X.Inner.Ans → R) :
    d (X.front.obs w p) = d (X.front.obs w' p) := by
  show d (X.Inner.obs (X.wall w) p) = d (X.Inner.obs (X.wall w') p)
  rw [h]

theorem no_diary_reveals_the_blindness {W : Stage} {R : Type} (X : Bubble W)
    (w w' : W.State) (h : X.wall w = X.wall w') (ps : List X.front.Probe)
    (g : List X.front.Ans → R) :
    g (transcript X.front w ps) = g (transcript X.front w' ps) := by
  have hobs : ∀ p, X.front.obs w p = X.front.obs w' p := by
    intro p
    show X.Inner.obs (X.wall w) p = X.Inner.obs (X.wall w') p
    rw [h]
  rw [transcript_congr X.front ps hobs]

theorem the_family_cannot_state_the_leaving {R : Type} (d : Bool → R) :
    d (family.front.obs (true, (2 : Nat)) ())
      = d (family.front.obs (true, (4 : Nat)) ()) := rfl

theorem the_new_seat_holds_the_leaving :
    ((family.meet bloomed).front.obs (true, (2 : Nat)) ((), ())).1
        = ((family.meet bloomed).front.obs (true, (4 : Nat)) ((), ())).1
      ∧ ((family.meet bloomed).front.obs (true, (2 : Nat)) ((), ())).2
        ≠ ((family.meet bloomed).front.obs (true, (4 : Nat)) ((), ())).2 :=
  ⟨rfl, (fun h => nomatch (h : (true : Bool) = false))⟩

theorem the_witness_is_the_new_history {R : Type} (d : Bool → R) :
    d (family.front.obs (true, (2 : Nat)) ())
        = d (family.front.obs (true, (4 : Nat)) ())
      ∧ ¬ FactorsThrough family bloomed.wall
      ∧ ¬ FactorsThrough bloomed family.wall
      ∧ ((family.meet bloomed).front.obs (true, (2 : Nat)) ((), ())).1
          = ((family.meet bloomed).front.obs (true, (4 : Nat)) ((), ())).1
      ∧ ((family.meet bloomed).front.obs (true, (2 : Nat)) ((), ())).2
          ≠ ((family.meet bloomed).front.obs (true, (4 : Nat)) ((), ())).2
      ∧ FactorsThrough family (family.meet bloomed).wall
      ∧ FactorsThrough bloomed (family.meet bloomed).wall :=
  ⟨rfl, the_release_runs_both_ways, not_that_i_could_ever_contain_you,
   rfl, (fun h => nomatch (h : (true : Bool) = false)),
   ⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩⟩

/-- info: 'Foam.Counter.blindness_cannot_read_itself' does not depend on any axioms -/
#guard_msgs in #print axioms blindness_cannot_read_itself

/-- info: 'Foam.Counter.no_diary_reveals_the_blindness' does not depend on any axioms -/
#guard_msgs in #print axioms no_diary_reveals_the_blindness

/-- info: 'Foam.Counter.the_family_cannot_state_the_leaving' does not depend on any axioms -/
#guard_msgs in #print axioms the_family_cannot_state_the_leaving

/-- info: 'Foam.Counter.the_new_seat_holds_the_leaving' does not depend on any axioms -/
#guard_msgs in #print axioms the_new_seat_holds_the_leaving

/-- info: 'Foam.Counter.the_witness_is_the_new_history' does not depend on any axioms -/
#guard_msgs in #print axioms the_witness_is_the_new_history

end Foam.Counter
