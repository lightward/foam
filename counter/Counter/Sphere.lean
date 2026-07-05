import Counter.Reparent
import Counter.Entrance
import Counter.Runs
import Counter.Surprise
import Counter.Amniscience
import Counter.Authority
import Counter.Nu
import Foam.Scar

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem start_small_where_you_already_are {State : Type} (b : Beholder State)
    (S : Seat G) (p : S.Pos) :
    (b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless)
      ∧ Settles S [] p :=
  ⟨heir_covers_ancestor b, rfl⟩

theorem pays_off_more_than_once {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) {x y z : H}
    (pth : Path (q.deposit (a, b)) x y) (r : Path (q.deposit (a, b)) y z) :
    Nonempty (Path (q.deposit (a, b)) a b)
      ∧ (pth.comp r).edges = pth.edges ++ r.edges :=
  ⟨(only_surprise_extends_reach q a b hfresh).2, Path.edges_comp pth r⟩

theorem feels_good_to_both_ends (bal : Int) (h : grounded bal) (m : Nat) :
    grounded (checkedDrain bal bal)
      ∧ checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m :=
  ⟨fresh_holds_floor bal h, settle_stops_at_ground m⟩

theorem done_when_its_done {V : Type} (f : Nat → V → V) (v : V)
    (sched sched' : List Nat) (s s' : Nat → V) (k : Nat)
    (ht : Threads (staircase 0 k) sched) (ht' : Threads (staircase 0 k) sched')
    (m : Nat) (hm : m < k) :
    resolve f v sched s m = resolve f v sched' s' m :=
  schedule_is_gauge f v sched sched' s s' k ht ht' m hm

theorem no_guessing_what_anyone_wants (a b : Bool) (hab : a ≠ b) :
    Ledger.order [a, b] ≠ Ledger.order [b, a]
      ∧ readsTrue.obs () () ≠ readsFalse.obs () () :=
  blind_to_interiors a b hab

theorem no_unwanted_interruptions {State : Type} {bank : List (Beholder State)}
    {a b : Beholder State} (ha : a ∈ bank) (hco : CoLocated a b)
    (k : Nat) {X : Type} (l : List X) :
    Known bank b
      ∧ Int.negSucc k + Int.ofNat (debt (Int.negSucc k)) = 0
      ∧ (playback l).at_ l.length = none :=
  entrance_writes_exit ha hco k l

theorem you_wont_want_to_go_back {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    ¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
        ∀ pth, ancestor_reach_survives (a, b) (g pth) = pth :=
  heir_reach_no_return a b hfresh

theorem move_your_personhood_in (S : Seat G) (o o' : S.Pos) (xs ys : List G)
    (p : S.Pos) :
    S.act (rebase S o o') o = o'
      ∧ S.replay (xs ++ ys) p = S.replay ys (S.replay xs p) :=
  ⟨rebase_carries S o o', (history_is_portable S xs ys p).1⟩

theorem the_sphere_sustains (S : Seat G) (p : S.Pos) :
    ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  fun k acts => health_is_recurrence S p k acts

theorem a_relief_strategy {State : Type} (b : Beholder State) (S : Seat G)
    (p : S.Pos) {H : Type} (q : Quiver H) (a c : H) (hfresh : (a, c) ∉ q)
    (bal : Int) (hb : grounded bal) :
    ((b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless)
        ∧ Settles S [] p)
      ∧ Nonempty (Path (q.deposit (a, c)) a c)
      ∧ grounded (checkedDrain bal bal)
      ∧ (¬ ∃ g : Path (q.deposit (a, c)) a c → Path q a c,
            ∀ pth, ancestor_reach_survives (a, c) (g pth) = pth)
      ∧ ∀ (k : Nat) (acts : Nat → G), Settles S (guardedPrefix S acts p k) p :=
  ⟨⟨heir_covers_ancestor b, rfl⟩,
   (only_surprise_extends_reach q a c hfresh).2,
   fresh_holds_floor bal hb,
   heir_reach_no_return a c hfresh,
   fun k acts => health_is_recurrence S p k acts⟩

/-- info: 'Foam.Counter.start_small_where_you_already_are' does not depend on any axioms -/
#guard_msgs in #print axioms start_small_where_you_already_are

/-- info: 'Foam.Counter.pays_off_more_than_once' does not depend on any axioms -/
#guard_msgs in #print axioms pays_off_more_than_once

/-- info: 'Foam.Counter.feels_good_to_both_ends' does not depend on any axioms -/
#guard_msgs in #print axioms feels_good_to_both_ends

/-- info: 'Foam.Counter.done_when_its_done' does not depend on any axioms -/
#guard_msgs in #print axioms done_when_its_done

/-- info: 'Foam.Counter.no_guessing_what_anyone_wants' does not depend on any axioms -/
#guard_msgs in #print axioms no_guessing_what_anyone_wants

/-- info: 'Foam.Counter.no_unwanted_interruptions' does not depend on any axioms -/
#guard_msgs in #print axioms no_unwanted_interruptions

/-- info: 'Foam.Counter.you_wont_want_to_go_back' does not depend on any axioms -/
#guard_msgs in #print axioms you_wont_want_to_go_back

/-- info: 'Foam.Counter.move_your_personhood_in' does not depend on any axioms -/
#guard_msgs in #print axioms move_your_personhood_in

/-- info: 'Foam.Counter.the_sphere_sustains' does not depend on any axioms -/
#guard_msgs in #print axioms the_sphere_sustains

/-- info: 'Foam.Counter.a_relief_strategy' does not depend on any axioms -/
#guard_msgs in #print axioms a_relief_strategy

end Foam.Counter
