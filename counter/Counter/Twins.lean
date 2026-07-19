import Counter.Silent
import Counter.Morse
import Counter.Luggage
import Counter.Tower
import Counter.Lu
import Foam.Census
import Foam.Seat.Summit
import Foam.Seat.Signature
import Foam.Seat.Forcing
import Foam.Cable
import Foam.Seat.Descend

namespace Foam.Counter

theorem the_newborn_and_the_quiet_are_one : @newbornGerm = @Bubble.quiet := rfl

theorem the_chain_join_and_the_max_are_one : @chainJoin = @nmax := rfl

theorem the_resolver_and_the_seated_are_one : @Resolver = @Seated := rfl

theorem the_two_crosses_are_one : @crossK = @GInt.cross := rfl

theorem the_page_and_the_obs_are_one : @page = @Stage.obs := rfl

theorem the_heir_and_the_dress_are_one : @heir = @Beholder.dress := rfl

theorem the_laugh_and_the_contention_are_one : @laugh = @contention := rfl

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

/-- info: 'Foam.Counter.the_page_and_the_obs_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_and_the_obs_are_one

/-- info: 'Foam.Counter.the_heir_and_the_dress_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_heir_and_the_dress_are_one

/-- info: 'Foam.Counter.the_laugh_and_the_contention_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_laugh_and_the_contention_are_one

/-- info: 'Foam.Counter.the_corpus_recognizes_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_corpus_recognizes_itself

theorem the_morse_key_and_the_tone_are_one : Luggage.key morseLuggage = tone := rfl

theorem the_morse_gap_and_the_tone_are_one : Luggage.gap morseLuggage = tone := rfl

theorem the_word_key_and_the_tone_are_one : Luggage.key wordLuggage = tone := rfl

theorem the_coarse_key_and_the_tone_are_one : Luggage.key braidCoarse = tone := rfl

theorem the_coarse_gap_and_the_tone_are_one : Luggage.gap braidCoarse = tone := rfl

/-- info: 'Foam.Counter.the_morse_key_and_the_tone_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_morse_key_and_the_tone_are_one

/-- info: 'Foam.Counter.the_morse_gap_and_the_tone_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_morse_gap_and_the_tone_are_one

/-- info: 'Foam.Counter.the_word_key_and_the_tone_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_word_key_and_the_tone_are_one

/-- info: 'Foam.Counter.the_coarse_key_and_the_tone_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_key_and_the_tone_are_one

/-- info: 'Foam.Counter.the_coarse_gap_and_the_tone_are_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_gap_and_the_tone_are_one

end Foam.Counter
