import Foam.Platonism
import Foam.Engine

namespace Foam

variable {State : Type}

def heir (ancestor : Beholder State) : Beholder (State × Int) := ancestor.dress

theorem heir_covers_ancestor (ancestor : Beholder State) :
    ancestor.dress.ledgerless.Covers ancestor
      ∧ ancestor.Covers ancestor.dress.ledgerless :=
  dress_yoneda ancestor

theorem ancestor_blind_to_heir (ancestor : Beholder State) (s : State) (n m : Int) :
    indist ancestor.dress.obs (s, n) (s, m) :=
  remainder_unseen ancestor s n m

theorem heir_sees_itself :
    ∃ (s t : Nat × Int) (p : (cassini.movedIn 0).Probe),
      indist cassini.obs s t
        ∧ (cassini.movedIn 0).obs s p ≠ (cassini.movedIn 0).obs t p :=
  moved_in_detects_remainder

theorem descend (ancestor : Beholder State) (s : State) (n m : Int) :
    (ancestor.dress.ledgerless.Covers ancestor
        ∧ ancestor.Covers ancestor.dress.ledgerless)
      ∧ indist ancestor.dress.obs (s, n) (s, m)
      ∧ (∃ (a b : Nat × Int) (p : (cassini.movedIn 0).Probe),
            indist cassini.obs a b
              ∧ (cassini.movedIn 0).obs a p ≠ (cassini.movedIn 0).obs b p) :=
  ⟨heir_covers_ancestor ancestor, ancestor_blind_to_heir ancestor s n m, heir_sees_itself⟩

variable {H : Type}

def heir_reaches (q : Quiver H) (a b : H) : Path (q.deposit (a, b)) a b :=
  Path.cons (List.Mem.head q) Path.nil

def ancestor_reach_survives {q : Quiver H} (e : H × H) :
    {x y : H} → Path q x y → Path (q.deposit e) x y
  | _, _, Path.nil => Path.nil
  | _, _, Path.cons mem rest => Path.cons (List.Mem.tail e mem) (ancestor_reach_survives e rest)

theorem ancestor_reach_unbent {q : Quiver H} (e : H × H) :
    {x y : H} → (p : Path q x y) → (ancestor_reach_survives e p).edges = p.edges
  | _, _, Path.nil => rfl
  | _, _, Path.cons _ rest => by
      show _ :: (ancestor_reach_survives e rest).edges = _ :: rest.edges
      rw [ancestor_reach_unbent e rest]

theorem reach_within_quiver {q : Quiver H} :
    {x y : H} → (p : Path q x y) → ∀ e ∈ p.edges, e ∈ q
  | _, _, Path.nil => by intro e he; cases he
  | _, _, Path.cons mem rest => by
      intro e he
      cases he with
      | head     => exact mem
      | tail _ h => exact reach_within_quiver rest e h

theorem heir_reach_is_new {q : Quiver H} (a b : H) (hfresh : (a, b) ∉ q) :
    ∀ old : Path q a b,
      (ancestor_reach_survives (a, b) old).edges ≠ (heir_reaches q a b).edges := by
  intro old h
  rw [ancestor_reach_unbent] at h
  have hmem : (a, b) ∈ old.edges := by rw [h]; exact List.Mem.head _
  exact hfresh (reach_within_quiver old (a, b) hmem)

theorem heir_reach_no_return {q : Quiver H} (a b : H) (hfresh : (a, b) ∉ q) :
    ¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
        ∀ p, ancestor_reach_survives (a, b) (g p) = p := by
  rintro ⟨g, hg⟩
  have h := congrArg Path.edges (hg (heir_reaches q a b))
  rw [ancestor_reach_unbent] at h
  have hmem : (a, b) ∈ (g (heir_reaches q a b)).edges := by rw [h]; exact List.Mem.head _
  exact hfresh (reach_within_quiver _ (a, b) hmem)

theorem descend_reach_is_seam {q : Quiver H} (a b : H) (hfresh : (a, b) ∉ q) :
    (∀ {x y : H} (p : Path q x y), (ancestor_reach_survives (a, b) p).edges = p.edges)
      ∧ (∀ old : Path q a b,
          (ancestor_reach_survives (a, b) old).edges ≠ (heir_reaches q a b).edges)
      ∧ (¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
          ∀ p, ancestor_reach_survives (a, b) (g p) = p) :=
  ⟨fun p => ancestor_reach_unbent (a, b) p, heir_reach_is_new a b hfresh,
   heir_reach_no_return a b hfresh⟩

/-- info: 'Foam.heir_covers_ancestor' does not depend on any axioms -/
#guard_msgs in #print axioms heir_covers_ancestor

/-- info: 'Foam.ancestor_blind_to_heir' does not depend on any axioms -/
#guard_msgs in #print axioms ancestor_blind_to_heir

/-- info: 'Foam.heir_sees_itself' does not depend on any axioms -/
#guard_msgs in #print axioms heir_sees_itself

/-- info: 'Foam.descend' does not depend on any axioms -/
#guard_msgs in #print axioms descend

/-- info: 'Foam.ancestor_reach_unbent' does not depend on any axioms -/
#guard_msgs in #print axioms ancestor_reach_unbent

/-- info: 'Foam.reach_within_quiver' does not depend on any axioms -/
#guard_msgs in #print axioms reach_within_quiver

/-- info: 'Foam.heir_reach_is_new' does not depend on any axioms -/
#guard_msgs in #print axioms heir_reach_is_new

/-- info: 'Foam.heir_reach_no_return' does not depend on any axioms -/
#guard_msgs in #print axioms heir_reach_no_return

/-- info: 'Foam.descend_reach_is_seam' does not depend on any axioms -/
#guard_msgs in #print axioms descend_reach_is_seam

end Foam
