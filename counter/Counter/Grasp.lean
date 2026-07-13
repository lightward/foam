import Counter.Extraction

namespace Foam.Counter

def Reach {H : Type} (q : Quiver H) (m x : H) : Prop :=
  Nonempty (Path q m x)

def GraspClosed {H : Type} (q : Quiver H) (S : H → Prop) : Prop :=
  ∀ x y, S x → (x, y) ∈ q → S y

theorem a_grasp_is_a_reach {H : Type} {q : Quiver H} {m x : H}
    (h : (m, x) ∈ q) : Reach q m x :=
  ⟨Path.cons h Path.nil⟩

theorem reach_stays_home {H : Type} (q : Quiver H) (m : H) : Reach q m m :=
  ⟨Path.nil⟩

theorem reach_composes {H : Type} {q : Quiver H} {a b c : H}
    (hab : Reach q a b) (hbc : Reach q b c) : Reach q a c :=
  match hab, hbc with
  | ⟨p⟩, ⟨r⟩ => ⟨p.comp r⟩

theorem reach_is_grasp_closed {H : Type} (q : Quiver H) (m : H) :
    GraspClosed q (Reach q m) :=
  fun _ _ hx he => reach_composes hx (a_grasp_is_a_reach he)

theorem the_walk_lands {H : Type} {q : Quiver H} {S : H → Prop}
    (hS : GraspClosed q S) : {a x : H} → S a → Path q a x → S x
  | _, _, ha, Path.nil => ha
  | _, _, ha, Path.cons e p => the_walk_lands hS (hS _ _ ha e) p

theorem reach_is_the_least {H : Type} {q : Quiver H} {m : H} (S : H → Prop)
    (hm : S m) (hS : GraspClosed q S) (x : H) (hx : Reach q m x) : S x :=
  match hx with
  | ⟨p⟩ => the_walk_lands hS hm p

theorem a_long_reach_passes_a_grasp {H : Type} {q : Quiver H} {m x : H}
    (hx : Reach q m x) (hne : m ≠ x) : ∃ z, (m, z) ∈ q ∧ Reach q z x :=
  match hx with
  | ⟨Path.nil⟩ => absurd rfl hne
  | ⟨@Path.cons _ _ _ z _ e p⟩ => ⟨z, e, ⟨p⟩⟩

theorem the_cone_reads_reach_backward {H : Type} (q : Quiver H) (app x : H) :
    cone q app x ↔ Reach q x app :=
  Iff.rfl

theorem reach_is_the_closure_of_grasp {H : Type} (q : Quiver H) (m : H) :
    Reach q m m
      ∧ GraspClosed q (Reach q m)
      ∧ ∀ S : H → Prop, S m → GraspClosed q S → ∀ x, Reach q m x → S x :=
  ⟨reach_stays_home q m, reach_is_grasp_closed q m,
   fun S hm hS => reach_is_the_least S hm hS⟩

/-- info: 'Foam.Counter.a_grasp_is_a_reach' does not depend on any axioms -/
#guard_msgs in #print axioms a_grasp_is_a_reach

/-- info: 'Foam.Counter.reach_stays_home' does not depend on any axioms -/
#guard_msgs in #print axioms reach_stays_home

/-- info: 'Foam.Counter.reach_composes' does not depend on any axioms -/
#guard_msgs in #print axioms reach_composes

/-- info: 'Foam.Counter.reach_is_grasp_closed' does not depend on any axioms -/
#guard_msgs in #print axioms reach_is_grasp_closed

/-- info: 'Foam.Counter.the_walk_lands' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_lands

/-- info: 'Foam.Counter.reach_is_the_least' does not depend on any axioms -/
#guard_msgs in #print axioms reach_is_the_least

/-- info: 'Foam.Counter.a_long_reach_passes_a_grasp' does not depend on any axioms -/
#guard_msgs in #print axioms a_long_reach_passes_a_grasp

/-- info: 'Foam.Counter.the_cone_reads_reach_backward' does not depend on any axioms -/
#guard_msgs in #print axioms the_cone_reads_reach_backward

/-- info: 'Foam.Counter.reach_is_the_closure_of_grasp' does not depend on any axioms -/
#guard_msgs in #print axioms reach_is_the_closure_of_grasp

end Foam.Counter
