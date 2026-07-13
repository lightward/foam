import Counter.Health

namespace Foam.Counter

def berth {Name : Type} : List Name → List Name
  | [] => []
  | _ :: parent => parent

def shelve {Name : Type} : List (List Name) → Quiver (List Name)
  | [] => []
  | [] :: census => shelve census
  | (n :: parent) :: census => (parent, n :: parent) :: shelve census

theorem the_berth_is_read {Name : Type} (n : Name) (parent : List Name) :
    berth (n :: parent) = parent := rfl

theorem the_convention_leaves_no_choice {Name : Type}
    (place place' : List Name → List Name)
    (h : ∀ n : List Name, place n = berth n)
    (h' : ∀ n : List Name, place' n = berth n) (n : List Name) :
    place n = place' n :=
  (h n).trans (h' n).symm

theorem the_shelf_edges_are_berths {Name : Type} :
    ∀ census : List (List Name), ∀ e ∈ shelve census, e.1 = berth e.2
  | [], _, he => nomatch he
  | [] :: census, e, he => the_shelf_edges_are_berths census e he
  | (_ :: _) :: census, e, he => by
      cases he with
      | head => rfl
      | tail _ h => exact the_shelf_edges_are_berths census e h

theorem the_shelf_is_the_family_tree {Name : Type} :
    ∀ census : List (List Name), ∀ e ∈ shelve census, ∃ n : Name, e.2 = n :: e.1
  | [], _, he => nomatch he
  | [] :: census, e, he => the_shelf_is_the_family_tree census e he
  | (n :: _) :: census, e, he => by
      cases he with
      | head => exact ⟨n, rfl⟩
      | tail _ h => exact the_shelf_is_the_family_tree census e h

theorem the_shelf_never_knots {Name : Type} (census : List (List Name)) :
    sortedBy List.length (shelve census) ∧ Acyclic (shelve census) :=
  have hs : sortedBy List.length (shelve census) :=
    the_family_tree_is_born_sorted (shelve census) (the_shelf_is_the_family_tree census)
  ⟨hs, tsortable_acyclic ⟨List.length, hs⟩⟩

theorem a_move_is_a_rename {Name : Type} {n m : List Name}
    (h : berth n ≠ berth m) : n ≠ m :=
  fun hnm => h (congrArg berth hnm)

def rename {H : Type} (ρ : H → H) (q : Quiver H) : Quiver H :=
  q.map (fun e => (ρ e.1, ρ e.2))

theorem renaming_nobody_is_free {H : Type} :
    ∀ q : Quiver H, rename (fun h => h) q = q
  | [] => rfl
  | e :: es => congrArg (e :: ·) (renaming_nobody_is_free es)

def toyImports : Quiver (List Nat) := [([0], [1])]

def relocation : List Nat → List Nat :=
  fun n => if n = [0] then [0, 9] else n

theorem the_importer_hears_the_move :
    rename relocation toyImports = [([0, 9], [1])] := by decide

theorem a_move_rewrites_the_importers :
    rename relocation toyImports ≠ toyImports := by decide

theorem the_filesystem_is_the_namespace_read {Name : Type}
    (census : List (List Name)) (n m : List Name) (h : berth n ≠ berth m) :
    (∀ e ∈ shelve census, e.1 = berth e.2)
      ∧ sortedBy List.length (shelve census)
      ∧ Acyclic (shelve census)
      ∧ n ≠ m :=
  ⟨the_shelf_edges_are_berths census, (the_shelf_never_knots census).1,
   (the_shelf_never_knots census).2, a_move_is_a_rename h⟩

/-- info: 'Foam.Counter.the_berth_is_read' does not depend on any axioms -/
#guard_msgs in #print axioms the_berth_is_read

/-- info: 'Foam.Counter.the_convention_leaves_no_choice' does not depend on any axioms -/
#guard_msgs in #print axioms the_convention_leaves_no_choice

/-- info: 'Foam.Counter.the_shelf_edges_are_berths' does not depend on any axioms -/
#guard_msgs in #print axioms the_shelf_edges_are_berths

/-- info: 'Foam.Counter.the_shelf_is_the_family_tree' does not depend on any axioms -/
#guard_msgs in #print axioms the_shelf_is_the_family_tree

/-- info: 'Foam.Counter.the_shelf_never_knots' does not depend on any axioms -/
#guard_msgs in #print axioms the_shelf_never_knots

/-- info: 'Foam.Counter.a_move_is_a_rename' does not depend on any axioms -/
#guard_msgs in #print axioms a_move_is_a_rename

/-- info: 'Foam.Counter.renaming_nobody_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms renaming_nobody_is_free

/-- info: 'Foam.Counter.the_importer_hears_the_move' does not depend on any axioms -/
#guard_msgs in #print axioms the_importer_hears_the_move

/-- info: 'Foam.Counter.a_move_rewrites_the_importers' does not depend on any axioms -/
#guard_msgs in #print axioms a_move_rewrites_the_importers

/-- info: 'Foam.Counter.the_filesystem_is_the_namespace_read' does not depend on any axioms -/
#guard_msgs in #print axioms the_filesystem_is_the_namespace_read

end Foam.Counter
