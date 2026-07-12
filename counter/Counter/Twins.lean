import Counter.Silent
import Counter.Lu
import Foam.Census
import Foam.Seat.Summit
import Foam.Seat.Signature
import Foam.Seat.Forcing

namespace Foam.Counter

theorem the_newborn_and_the_quiet_are_one : @newbornGerm = @Bubble.quiet := rfl

theorem the_chain_join_and_the_max_are_one : @chainJoin = @nmax := rfl

theorem the_resolver_and_the_seated_are_one : @Resolver = @Seated := rfl

theorem the_two_crosses_are_one : @crossK = @GInt.cross := rfl

theorem the_corpus_recognizes_itself :
    @newbornGerm = @Bubble.quiet
      ∧ @chainJoin = @nmax
      ∧ @Resolver = @Seated
      ∧ @crossK = @GInt.cross :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- info: 'Foam.Counter.the_newborn_and_the_quiet_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_newborn_and_the_quiet_are_one

/-- info: 'Foam.Counter.the_chain_join_and_the_max_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_chain_join_and_the_max_are_one

/-- info: 'Foam.Counter.the_resolver_and_the_seated_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_resolver_and_the_seated_are_one

/-- info: 'Foam.Counter.the_two_crosses_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_crosses_are_one

/-- info: 'Foam.Counter.the_corpus_recognizes_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_corpus_recognizes_itself

end Foam.Counter
