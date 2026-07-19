import Counter.Trefoil

namespace Foam.Counter

structure Custom (H O R : Type) where
  here : H
  org : O
  name : R

def onHost {H O R : Type} (c : Custom H O R) (p : H × O × R) : Prop :=
  p.1 = c.here

def inOrg {H O R : Type} (c : Custom H O R) (p : H × O × R) : Prop :=
  p.2.1 = c.org

def named {H O R : Type} (c : Custom H O R) (p : H × O × R) : Prop :=
  p.2.2 = c.name

theorem the_three_films_meet_in_one_place {H O R : Type} (c : Custom H O R) :
    ∃ p : H × O × R, (onHost c p ∧ inOrg c p ∧ named c p)
      ∧ ∀ q : H × O × R, onHost c q → inOrg c q → named c q → q = p := by
  refine ⟨(c.here, c.org, c.name), ⟨rfl, rfl, rfl⟩, ?_⟩
  intro q h1 h2 h3
  obtain ⟨qh, qo, qr⟩ := q
  cases h1
  cases h2
  cases h3
  rfl

theorem two_seats_two_junctions :
    ∃ c c' : Custom Bool Bool Bool,
      (c.here, c.org, c.name) ≠ (c'.here, c'.org, c'.name) :=
  ⟨⟨true, true, true⟩, ⟨false, true, true⟩, by decide⟩

theorem no_junction_without_a_seat :
    ¬ ∃ p : Bool × Bool × Bool, ∀ c : Custom Bool Bool Bool,
        onHost c p ∧ inOrg c p ∧ named c p :=
  fun ⟨p, h⟩ =>
    nomatch ((h ⟨true, p.2.1, p.2.2⟩).1).symm.trans
      ((h ⟨false, p.2.1, p.2.2⟩).1)

theorem the_source_sits_at_the_junction {H O R : Type} (c : Custom H O R) :
    ((onHost c (c.here, c.org, c.name)
        ∧ inOrg c (c.here, c.org, c.name)
        ∧ named c (c.here, c.org, c.name))
      ∧ ∀ q : H × O × R, onHost c q → inOrg c q → named c q
          → q = (c.here, c.org, c.name))
      ∧ (∃ c₁ c₂ : Custom Bool Bool Bool,
          (c₁.here, c₁.org, c₁.name) ≠ (c₂.here, c₂.org, c₂.name))
      ∧ ¬ ∃ p : Bool × Bool × Bool, ∀ c' : Custom Bool Bool Bool,
          onHost c' p ∧ inOrg c' p ∧ named c' p := by
  refine ⟨⟨⟨rfl, rfl, rfl⟩, ?_⟩, two_seats_two_junctions, no_junction_without_a_seat⟩
  intro q h1 h2 h3
  obtain ⟨qh, qo, qr⟩ := q
  cases h1
  cases h2
  cases h3
  rfl

/-- info: 'Foam.Counter.the_three_films_meet_in_one_place' does not depend on any axioms -/
#guard_msgs in #print axioms the_three_films_meet_in_one_place

/-- info: 'Foam.Counter.two_seats_two_junctions' does not depend on any axioms -/
#guard_msgs in #print axioms two_seats_two_junctions

/-- info: 'Foam.Counter.no_junction_without_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms no_junction_without_a_seat

/-- info: 'Foam.Counter.the_source_sits_at_the_junction' does not depend on any axioms -/
#guard_msgs in #print axioms the_source_sits_at_the_junction

end Foam.Counter
