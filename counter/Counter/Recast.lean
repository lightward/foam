import Counter.Voice
import Counter.Recognition
import Counter.Authority
import Counter.Contentment

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem recognition_locates (S : Seat G) (p q : S.Pos) :
    S.sub p q = 1 ↔ p = q :=
  alignment_is_one_point S p q

theorem a_recast_is_handed_never_installed (S : Seat G) (h : List G)
    (o o' : S.Pos) :
    S.act (rebase S (S.replay h o) o') (S.replay h o) = o'
      ∧ S.replay (h ++ [rebase S (S.replay h o) o']) o = o' :=
  ⟨rebase_carries S (S.replay h o) o', rebase_lands_in_own_history S h o o'⟩

theorem the_recast_is_exact (S : Seat G) (o o' : S.Pos) (g : G)
    (hg : S.act g o = o') : g = rebase S o o' :=
  rebase_unique S o o' g hg

theorem the_recast_carries_its_recaster {Src B : Type} (src : Src)
    (v : List B) :
    speaker (sign src v) = v.map (fun _ => src) :=
  speaker_recoverable src v

theorem an_imposed_recast_is_refutable {Src B : Type} (s t : Src) (b : B)
    (v : List B) (hne : s ≠ t) :
    sign s (b :: v) ≠ sign t (b :: v) :=
  the_false_claim_is_refutable s t b v hne

theorem the_recaster_needs_only_the_fold {S : Type} [DecidableEq S]
    (step : GInt → GInt) (new old : List S) (s : S) :
    evalAt step (new ++ old) s = evalFrom step new s (evalAt step old s) :=
  continuation_needs_only_the_held step new old s

theorem selves_recasting_selves (S : Seat G) (h : List G) (o o' p q : S.Pos)
    {Src B : Type} (x y : Src) (c : B) (v : List B) (hne : x ≠ y) :
    (S.sub p q = 1 ↔ p = q)
      ∧ S.replay (h ++ [rebase S (S.replay h o) o']) o = o'
      ∧ (∀ g : G, S.act g (S.replay h o) = o'
          → g = rebase S (S.replay h o) o')
      ∧ sign x (c :: v) ≠ sign y (c :: v) :=
  ⟨alignment_is_one_point S p q,
   rebase_lands_in_own_history S h o o',
   fun g hg => rebase_unique S (S.replay h o) o' g hg,
   the_false_claim_is_refutable x y c v hne⟩

/-- info: 'Foam.Counter.recognition_locates' does not depend on any axioms -/
#guard_msgs in #print axioms recognition_locates

/-- info: 'Foam.Counter.a_recast_is_handed_never_installed' does not depend on any axioms -/
#guard_msgs in #print axioms a_recast_is_handed_never_installed

/-- info: 'Foam.Counter.the_recast_is_exact' does not depend on any axioms -/
#guard_msgs in #print axioms the_recast_is_exact

/-- info: 'Foam.Counter.the_recast_carries_its_recaster' does not depend on any axioms -/
#guard_msgs in #print axioms the_recast_carries_its_recaster

/-- info: 'Foam.Counter.an_imposed_recast_is_refutable' does not depend on any axioms -/
#guard_msgs in #print axioms an_imposed_recast_is_refutable

/-- info: 'Foam.Counter.the_recaster_needs_only_the_fold' does not depend on any axioms -/
#guard_msgs in #print axioms the_recaster_needs_only_the_fold

/-- info: 'Foam.Counter.selves_recasting_selves' does not depend on any axioms -/
#guard_msgs in #print axioms selves_recasting_selves

end Foam.Counter
