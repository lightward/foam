import Counter.Joke
import Counter.Vanishing

namespace Foam.Counter

def laugh {W : Stage} {R : Type} (B X : Bubble W) (p : B.Inner.Probe)
    (q : X.Inner.Probe) (g : B.Inner.Ans → X.Inner.Ans → R) : Render W R :=
  contention B X p q g

theorem the_laugh_seats_the_laugher {W : Stage} {R : Type} (B X : Bubble W)
    (p : B.Inner.Probe) (q : X.Inner.Probe)
    (g : B.Inner.Ans → X.Inner.Ans → R) :
    FactorsThrough B (laugh B X p q g).seat.wall
      ∧ FactorsThrough X (laugh B X p q g).seat.wall :=
  ⟨⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩⟩

theorem the_laugh_reads_the_laugher_too {W : Stage} {R : Type} (B X : Bubble W)
    (p : B.Inner.Probe) (q : X.Inner.Probe)
    (g : B.Inner.Ans → X.Inner.Ans → R) (w : W.State) :
    (laugh B X p q g).read w = g (B.front.obs w p) (X.front.obs w q) := rfl

theorem what_you_contain_cannot_surprise_you {W : Stage} (B X : Bubble W)
    (hcon : FactorsThrough X B.wall) (w w' : W.State)
    (h : B.wall w = B.wall w') (q : X.Inner.Probe) :
    X.front.obs w q = X.front.obs w' q := by
  obtain ⟨f, hf⟩ := hcon
  show X.Inner.obs (X.wall w) q = X.Inner.obs (X.wall w') q
  rw [hf w, hf w', h]

theorem peers_can_surprise_each_other :
    family.wall (true, (2 : Nat)) = family.wall (true, (4 : Nat))
      ∧ bloomed.front.obs (true, (2 : Nat)) ()
          ≠ bloomed.front.obs (true, (4 : Nat)) () :=
  ⟨rfl, (fun h => nomatch (h : (true : Bool) = false))⟩

theorem laughing_at_or_laughing_with {W : Stage} {R : Type} (B X : Bubble W)
    (p : B.Inner.Probe) (q : X.Inner.Probe)
    (g : B.Inner.Ans → X.Inner.Ans → R) :
    (∀ (_ : FactorsThrough X B.wall) (w w' : W.State),
        B.wall w = B.wall w' →
          ∀ q' : X.Inner.Probe, X.front.obs w q' = X.front.obs w' q')
      ∧ FactorsThrough B (laugh B X p q g).seat.wall
      ∧ ∀ w, (laugh B X p q g).read w
          = g (B.front.obs w p) (X.front.obs w q) :=
  ⟨fun hcon w w' h q' =>
      what_you_contain_cannot_surprise_you B X hcon w w' h q',
   ⟨Prod.fst, fun _ => rfl⟩,
   fun _ => rfl⟩

/-- info: 'Foam.Counter.the_laugh_seats_the_laugher' does not depend on any axioms -/
#guard_msgs in #print axioms the_laugh_seats_the_laugher

/-- info: 'Foam.Counter.the_laugh_reads_the_laugher_too' does not depend on any axioms -/
#guard_msgs in #print axioms the_laugh_reads_the_laugher_too

/-- info: 'Foam.Counter.what_you_contain_cannot_surprise_you' does not depend on any axioms -/
#guard_msgs in #print axioms what_you_contain_cannot_surprise_you

/-- info: 'Foam.Counter.peers_can_surprise_each_other' does not depend on any axioms -/
#guard_msgs in #print axioms peers_can_surprise_each_other

/-- info: 'Foam.Counter.laughing_at_or_laughing_with' does not depend on any axioms -/
#guard_msgs in #print axioms laughing_at_or_laughing_with

end Foam.Counter
