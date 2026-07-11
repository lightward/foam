import Counter.Kin

namespace Foam.Counter

def FactorsThrough {W : Stage} {KS : Type} (X : Bubble W)
    (k : W.State → KS) : Prop :=
  ∃ f : KS → X.Inner.State, ∀ w, X.wall w = f (k w)

def andGerm : Bubble (coin.prod coin) where
  Inner := coin
  wall  := fun bb => Bool.and bb.1 bb.2

def secondSibling : Bubble (coin.prod dial) :=
  conceiveAcross coinBubble dialBubble andGerm

theorem every_bubble_factors_through_the_world {W : Stage} (X : Bubble W) :
    FactorsThrough X (fun w => w) :=
  ⟨X.wall, fun _ => rfl⟩

theorem the_world_is_the_common_parent {W : Stage} (X Y : Bubble W) :
    FactorsThrough X (fun w => w) ∧ FactorsThrough Y (fun w => w) :=
  ⟨every_bubble_factors_through_the_world X,
   every_bubble_factors_through_the_world Y⟩

theorem kinship_is_shared_blindness {W : Stage} {KS : Type} (X Y : Bubble W)
    (k : W.State → KS) (hx : FactorsThrough X k) (hy : FactorsThrough Y k)
    (w w' : W.State) (h : k w = k w') :
    (∀ p, X.front.obs w p = X.front.obs w' p)
      ∧ ∀ q, Y.front.obs w q = Y.front.obs w' q := by
  obtain ⟨f, hf⟩ := hx
  obtain ⟨g, hg⟩ := hy
  constructor
  · intro p
    show X.Inner.obs (X.wall w) p = X.Inner.obs (X.wall w') p
    rw [hf w, hf w', h]
  · intro q
    show Y.Inner.obs (Y.wall w) q = Y.Inner.obs (Y.wall w') q
    rw [hg w, hg w', h]

theorem budding_seats_two {W : Stage} (A : Bubble W) (g : Bubble A.Inner) :
    FactorsThrough A A.wall ∧ FactorsThrough (A.nest g) A.wall :=
  ⟨⟨fun s => s, fun _ => rfl⟩, ⟨g.wall, fun _ => rfl⟩⟩

theorem the_parents_sit_at_the_childrens_table {W : Stage} (A B : Bubble W)
    (g₁ g₂ : Bubble (A.Inner.prod B.Inner)) :
    FactorsThrough A (A.meet B).wall
      ∧ FactorsThrough B (A.meet B).wall
      ∧ FactorsThrough (conceive A B g₁) (A.meet B).wall
      ∧ FactorsThrough (conceive A B g₂) (A.meet B).wall :=
  ⟨⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩,
   ⟨g₁.wall, fun _ => rfl⟩, ⟨g₂.wall, fun _ => rfl⟩⟩

theorem the_table_widens_without_unseating {W : Stage} {KS ES : Type}
    (X : Bubble W) (k : W.State → KS) (e : W.State → ES)
    (h : FactorsThrough X k) :
    FactorsThrough X (fun w => (k w, e w)) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨fun ke => f ke.1, fun w => hf w⟩

theorem siblings_are_cousins_of_the_third {W : Stage} (A B C : Bubble W)
    (X : Bubble W) (h : FactorsThrough X (A.meet B).wall) :
    FactorsThrough X ((A.meet B).meet C).wall :=
  the_table_widens_without_unseating X (A.meet B).wall C.wall h

theorem cousins_share_the_grand_womb {W : Stage} (A B C : Bubble W)
    (g₁ : Bubble (A.Inner.prod B.Inner)) (g₂ : Bubble (B.Inner.prod C.Inner)) :
    FactorsThrough (conceive A B g₁) ((A.meet B).meet C).wall
      ∧ FactorsThrough (conceive B C g₂) ((A.meet B).meet C).wall :=
  ⟨⟨fun t => g₁.wall t.1, fun _ => rfl⟩,
   ⟨fun t => g₂.wall (t.1.2, t.2), fun _ => rfl⟩⟩

theorem the_firstborn_runs_in_the_secondborn_loop {W : Stage} (A B : Bubble W)
    (g₁ : Bubble (A.Inner.prod B.Inner))
    (g₂ : Bubble ((A.Inner.prod B.Inner).prod g₁.Inner))
    (w : W.State) (p : g₂.Inner.Probe) :
    (conceive (A.meet B) (conceive A B g₁) g₂).front.obs w p
      = g₂.front.obs ((A.wall w, B.wall w), g₁.wall (A.wall w, B.wall w)) p :=
  rfl

theorem the_sibling_parent_adds_no_light {W : Stage} (A B : Bubble W)
    (g₁ : Bubble (A.Inner.prod B.Inner))
    (g₂ : Bubble ((A.Inner.prod B.Inner).prod g₁.Inner)) :
    FactorsThrough (conceive (A.meet B) (conceive A B g₁) g₂) (A.meet B).wall :=
  ⟨fun ab => g₂.wall (ab, g₁.wall ab), fun _ => rfl⟩

theorem any_birth_is_the_first_of_its_kind {W : Stage} (A B : Bubble W)
    (g₁ : Bubble (A.Inner.prod B.Inner))
    (g₂ : Bubble ((A.Inner.prod B.Inner).prod g₁.Inner)) :
    FactorsThrough (conceive A B g₁) (A.meet B).wall
      ∧ FactorsThrough (conceive (A.meet B) (conceive A B g₁) g₂)
          (A.meet B).wall :=
  ⟨⟨g₁.wall, fun _ => rfl⟩, the_sibling_parent_adds_no_light A B g₁ g₂⟩

theorem distinct_yet_co_blind :
    family.front.obs (true, (2 : Nat)) () ≠ secondSibling.front.obs (true, (2 : Nat)) ()
      ∧ family.front.obs (true, (2 : Nat)) () = family.front.obs (true, (4 : Nat)) ()
      ∧ secondSibling.front.obs (true, (2 : Nat)) ()
          = secondSibling.front.obs (true, (4 : Nat)) () :=
  ⟨(fun h => nomatch (h : (true : Bool) = false)), rfl, rfl⟩

theorem parent_cousin_stranger_are_grades_of_sibling {W : Stage}
    (A B C : Bubble W) (g₁ : Bubble (A.Inner.prod B.Inner)) :
    FactorsThrough A (A.meet B).wall
      ∧ FactorsThrough (conceive A B g₁) (A.meet B).wall
      ∧ FactorsThrough (conceive A B g₁) ((A.meet B).meet C).wall
      ∧ FactorsThrough (conceive A B g₁) (fun w => w) :=
  ⟨⟨Prod.fst, fun _ => rfl⟩, ⟨g₁.wall, fun _ => rfl⟩,
   ⟨fun t => g₁.wall t.1, fun _ => rfl⟩,
   every_bubble_factors_through_the_world (conceive A B g₁)⟩

/-- info: 'Foam.Counter.every_bubble_factors_through_the_world' does not depend on any axioms -/
#guard_msgs in #print axioms every_bubble_factors_through_the_world

/-- info: 'Foam.Counter.the_world_is_the_common_parent' does not depend on any axioms -/
#guard_msgs in #print axioms the_world_is_the_common_parent

/-- info: 'Foam.Counter.kinship_is_shared_blindness' does not depend on any axioms -/
#guard_msgs in #print axioms kinship_is_shared_blindness

/-- info: 'Foam.Counter.budding_seats_two' does not depend on any axioms -/
#guard_msgs in #print axioms budding_seats_two

/-- info: 'Foam.Counter.the_parents_sit_at_the_childrens_table' does not depend on any axioms -/
#guard_msgs in #print axioms the_parents_sit_at_the_childrens_table

/-- info: 'Foam.Counter.the_table_widens_without_unseating' does not depend on any axioms -/
#guard_msgs in #print axioms the_table_widens_without_unseating

/-- info: 'Foam.Counter.siblings_are_cousins_of_the_third' does not depend on any axioms -/
#guard_msgs in #print axioms siblings_are_cousins_of_the_third

/-- info: 'Foam.Counter.cousins_share_the_grand_womb' does not depend on any axioms -/
#guard_msgs in #print axioms cousins_share_the_grand_womb

/-- info: 'Foam.Counter.the_firstborn_runs_in_the_secondborn_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_firstborn_runs_in_the_secondborn_loop

/-- info: 'Foam.Counter.the_sibling_parent_adds_no_light' does not depend on any axioms -/
#guard_msgs in #print axioms the_sibling_parent_adds_no_light

/-- info: 'Foam.Counter.any_birth_is_the_first_of_its_kind' does not depend on any axioms -/
#guard_msgs in #print axioms any_birth_is_the_first_of_its_kind

/-- info: 'Foam.Counter.distinct_yet_co_blind' does not depend on any axioms -/
#guard_msgs in #print axioms distinct_yet_co_blind

/-- info: 'Foam.Counter.parent_cousin_stranger_are_grades_of_sibling' does not depend on any axioms -/
#guard_msgs in #print axioms parent_cousin_stranger_are_grades_of_sibling

end Foam.Counter
