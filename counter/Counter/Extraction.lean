import Counter.Shelf

namespace Foam.Counter

def cone {H : Type} (q : Quiver H) (app : H) : H → Prop :=
  fun x => Nonempty (Path q x app)

def SelfContained {H : Type} (q : Quiver H) (S : H → Prop) : Prop :=
  ∀ e ∈ q, S e.2 → S e.1

def Extractable {H : Type} (q : Quiver H) (app : H) (S : H → Prop) : Prop :=
  SelfContained q S ∧ ∀ x, S x → cone q app x

def commons {H : Type} (q : Quiver H) (a b : H) : H → Prop :=
  fun x => cone q a x ∧ cone q b x

theorem the_app_anchors_its_cone {H : Type} (q : Quiver H) (app : H) :
    cone q app app :=
  ⟨Path.nil⟩

theorem the_cone_is_self_contained {H : Type} (q : Quiver H) (app : H) :
    SelfContained q (cone q app) := by
  intro e he hS
  obtain ⟨p⟩ := hS
  exact ⟨Path.cons he p⟩

theorem one_app_extracts_everything {H : Type} (q : Quiver H) (app : H) :
    Extractable q app (cone q app)
      ∧ ∀ S : H → Prop, Extractable q app S → ∀ x, S x → cone q app x :=
  ⟨⟨the_cone_is_self_contained q app, fun _ h => h⟩, fun _ hS => hS.2⟩

theorem the_commons_is_self_contained {H : Type} (q : Quiver H) (a b : H) :
    SelfContained q (commons q a b) :=
  fun e he h =>
    ⟨the_cone_is_self_contained q a e he h.1, the_cone_is_self_contained q b e he h.2⟩

theorem the_commons_is_extractable_from_both {H : Type} (q : Quiver H) (a b : H) :
    Extractable q a (commons q a b) ∧ Extractable q b (commons q a b) :=
  ⟨⟨the_commons_is_self_contained q a b, fun _ h => h.1⟩,
   ⟨the_commons_is_self_contained q a b, fun _ h => h.2⟩⟩

theorem the_commons_is_the_largest_shared {H : Type} (q : Quiver H) (a b : H)
    (S : H → Prop) (hA : Extractable q a S) (hB : Extractable q b S) :
    ∀ x, S x → commons q a b x :=
  fun x hx => ⟨hA.2 x hx, hB.2 x hx⟩

def basecamp : Quiver Nat := [(0, 1), (1, 2), (0, 3)]

def baseOnly : Nat → Prop := fun x => x = 0

def baseAndMid : Nat → Prop := fun x => x = 0 ∨ x = 1

def reach02 : Path basecamp 0 2 :=
  Path.cons (List.Mem.head _) (Path.cons (List.Mem.tail _ (List.Mem.head _)) Path.nil)

def reach12 : Path basecamp 1 2 :=
  Path.cons (List.Mem.tail _ (List.Mem.head _)) Path.nil

theorem base_only_extracts : Extractable basecamp 2 baseOnly := by
  constructor
  · intro e he
    cases he with
    | head => exact fun h => nomatch h
    | tail _ h1 =>
        cases h1 with
        | head => exact fun h => nomatch h
        | tail _ h2 =>
            cases h2 with
            | head => exact fun h => nomatch h
            | tail _ h3 => exact nomatch h3
  · intro x hx
    cases hx
    exact ⟨reach02⟩

theorem base_and_mid_extracts : Extractable basecamp 2 baseAndMid := by
  constructor
  · intro e he
    cases he with
    | head => exact fun _ => Or.inl rfl
    | tail _ h1 =>
        cases h1 with
        | head => exact fun h => absurd h (show ¬((2 : Nat) = 0 ∨ (2 : Nat) = 1) by decide)
        | tail _ h2 =>
            cases h2 with
            | head => exact fun h => absurd h (show ¬((3 : Nat) = 0 ∨ (3 : Nat) = 1) by decide)
            | tail _ h3 => exact nomatch h3
  · intro x hx
    cases hx with
    | inl h => cases h; exact ⟨reach02⟩
    | inr h => cases h; exact ⟨reach12⟩

theorem one_app_pins_nothing :
    Extractable basecamp 2 baseOnly ∧ Extractable basecamp 2 baseAndMid
      ∧ baseAndMid 1 ∧ ¬ baseOnly 1 :=
  ⟨base_only_extracts, base_and_mid_extracts, Or.inr rfl, fun h => nomatch h⟩

def basecampChart : Nat → Nat :=
  fun x => if x = 2 then 2 else if x = 0 then 0 else 1

theorem basecamp_sorted : sortedBy basecampChart basecamp := by
  intro e he
  cases he with
  | head => decide
  | tail _ h1 =>
      cases h1 with
      | head => decide
      | tail _ h2 =>
          cases h2 with
          | head => decide
          | tail _ h3 => exact nomatch h3

theorem the_empty_walk_stays_home {H : Type} {q : Quiver H} :
    {a b : H} → (p : Path q a b) → p.edges = [] → a = b
  | _, _, Path.nil, _ => rfl
  | _, _, Path.cons _ _, h => nomatch h

theorem mid_walks_only_upward (p : Path basecamp 1 3) : p.edges ≠ [] :=
  fun h => absurd (the_empty_walk_stays_home p h) (by decide)

theorem the_base_is_common : commons basecamp 2 3 0 :=
  ⟨⟨reach02⟩, ⟨Path.cons (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) Path.nil⟩⟩

theorem the_second_app_draws_the_boundary :
    cone basecamp 2 1 ∧ ¬ commons basecamp 2 3 1 := by
  constructor
  · exact ⟨reach12⟩
  · intro h
    obtain ⟨p⟩ := h.2
    exact absurd (path_climbs basecamp_sorted p (mid_walks_only_upward p)) (by decide)

theorem activefoam_is_read_at_the_commons {H : Type} (q : Quiver H) (a b : H) :
    (Extractable q a (commons q a b) ∧ Extractable q b (commons q a b))
      ∧ (∀ S : H → Prop, Extractable q a S → Extractable q b S →
          ∀ x, S x → commons q a b x)
      ∧ (Extractable basecamp 2 baseOnly ∧ Extractable basecamp 2 baseAndMid
          ∧ baseAndMid 1 ∧ ¬ baseOnly 1)
      ∧ (cone basecamp 2 1 ∧ ¬ commons basecamp 2 3 1) :=
  ⟨the_commons_is_extractable_from_both q a b,
   the_commons_is_the_largest_shared q a b,
   one_app_pins_nothing,
   the_second_app_draws_the_boundary⟩

/-- info: 'Foam.Counter.the_app_anchors_its_cone' does not depend on any axioms -/
#guard_msgs in #print axioms the_app_anchors_its_cone

/-- info: 'Foam.Counter.the_cone_is_self_contained' does not depend on any axioms -/
#guard_msgs in #print axioms the_cone_is_self_contained

/-- info: 'Foam.Counter.one_app_extracts_everything' does not depend on any axioms -/
#guard_msgs in #print axioms one_app_extracts_everything

/-- info: 'Foam.Counter.the_commons_is_self_contained' does not depend on any axioms -/
#guard_msgs in #print axioms the_commons_is_self_contained

/-- info: 'Foam.Counter.the_commons_is_extractable_from_both' does not depend on any axioms -/
#guard_msgs in #print axioms the_commons_is_extractable_from_both

/-- info: 'Foam.Counter.the_commons_is_the_largest_shared' does not depend on any axioms -/
#guard_msgs in #print axioms the_commons_is_the_largest_shared

/-- info: 'Foam.Counter.base_only_extracts' does not depend on any axioms -/
#guard_msgs in #print axioms base_only_extracts

/-- info: 'Foam.Counter.base_and_mid_extracts' does not depend on any axioms -/
#guard_msgs in #print axioms base_and_mid_extracts

/-- info: 'Foam.Counter.one_app_pins_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms one_app_pins_nothing

/-- info: 'Foam.Counter.basecamp_sorted' does not depend on any axioms -/
#guard_msgs in #print axioms basecamp_sorted

/-- info: 'Foam.Counter.the_empty_walk_stays_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_empty_walk_stays_home

/-- info: 'Foam.Counter.mid_walks_only_upward' does not depend on any axioms -/
#guard_msgs in #print axioms mid_walks_only_upward

/-- info: 'Foam.Counter.the_base_is_common' does not depend on any axioms -/
#guard_msgs in #print axioms the_base_is_common

/-- info: 'Foam.Counter.the_second_app_draws_the_boundary' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_app_draws_the_boundary

/-- info: 'Foam.Counter.activefoam_is_read_at_the_commons' does not depend on any axioms -/
#guard_msgs in #print axioms activefoam_is_read_at_the_commons

end Foam.Counter
