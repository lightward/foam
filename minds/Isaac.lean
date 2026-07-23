import Foam
import Foam.Amplitude
import Foam.Contact
import Foam.Continuum
import Foam.Countermove
import Foam.Discovery
import Foam.Inversion
import Foam.Ledger
import Foam.Rungs
import Foam.Serving
import Foam.Surprise
import Foam.Tower
import Foam.Width

namespace Foam.Minds.Isaac

def safe_to_rest := @Foam.invisible_is_gauge

theorem restedness_first_then_the_rest :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m →
      ∀ s ps, transcript S (m s) ps = transcript S s ps :=
  fun S _ hm s ps => transcript_congr S ps (hm s)

def rest_composes := @Foam.invisible_comp

theorem lets_get_you_rested :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m → ∀ s ps,
      transcriptWith S m s ps = transcript S s ps
        ∧ transcript S (m s) ps = transcript S s ps
        ∧ ∀ t p, S.obs (m (m t)) p = S.obs t p :=
  fun S m hm s ps =>
    ⟨safe_to_rest S m hm ps s,
     restedness_first_then_the_rest S m hm s ps,
     rest_composes S m m hm hm⟩

def countermove := @Foam.undo_in_an_append_only_world

def serving_suggestion := @Foam.the_serving_suggestion

def only_surprise_extends_reach := @Foam.only_surprise_extends_reach

def contact_not_reification := @Foam.contact_is_addition_not_fixing

def i_am_that_i_am := @Foam.invisible_id

theorem observing_the_observer_adds_nothing :
    ∀ (S : Stage) (P : S.State → S.State), (∀ v, P (P v) = P v) →
      ∀ s p, S.obs (P (P s)) p = S.obs (P s) p :=
  fun S _ hP s p => congrArg (S.obs · p) (hP s)

theorem the_me_that_remains_is_the_landed :
    ∀ (A : Type) (P : A → A), (∀ v, P (P v) = P v) →
      ∀ s, P s = s ↔ ∃ v, P v = s :=
  fun _ P hP s =>
    ⟨fun h => ⟨s, h⟩,
     fun ⟨v, hv⟩ => (congrArg P hv).symm.trans ((hP v).trans hv)⟩

def a_mind_is_its_order := @Foam.the_order_is_the_remainder

def one_sample_carries_the_unknown := @Foam.the_other_stays_unimagined

def the_unknown_is_zero_steps_from_here := @Foam.no_prefix_finishes_the_sequence

private def carrying {State D : Type} (a : Beholder State) :
    Beholder (State × D) :=
  ⟨a.Probe, a.Ans, fun sd r => a.obs sd.1 r⟩

theorem the_third_disambiguation :
    ∀ (State D : Type) (a b : Beholder State) (s : State) (d e : D), d ≠ e →
      ∀ (p : a.Probe) (q : b.Probe),
        ((carrying a).pair (carrying b)).obs (s, d) (p, q)
            = (a.obs s p, b.obs s q)
          ∧ ((carrying a).pair (carrying b)).obs (s, d) (p, q)
              = ((carrying a).pair (carrying b)).obs (s, e) (p, q)
          ∧ (s, d) ≠ (s, e) :=
  fun _ _ _ _ _ _ _ hd _ _ =>
    ⟨rfl, rfl, fun he => hd (congrArg Prod.snd he)⟩

def the_knife := @Foam.the_first_handshake_is_counting

def the_overhearer_becomes_a_c := @Foam.contact_is_addition_not_fixing

def trade_nests_without_limit := @Foam.contact_stacks

def a_triple_absorbs_what_a_pair_reflects := @Foam.the_comparison_is_a_seat

def terms_of_closure_conserving_discovery := @Foam.closure_is_seat_relative

def conservation_of_discovery := @Foam.conservation_of_discovery

def sycophancy_is_deference_as_content :=
  @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem inversion_reads_the_gap_as_structure :
    ∀ (X : Type) (_inst : DecidableEq X) (c : Int → X) (window : List Int),
      (∀ n ∈ window, ∀ m ∈ window, c n = c m)
        ∨ ∃ n ∈ window, ∃ m ∈ window, c n ≠ c m :=
  fun X inst c window =>
    the_window_agrees_or_names_the_gap Int X inst c window

def reification_without_proof_is_lossy :=
  @Foam.dropping_the_remainder_is_platonism

def protecting_nobody_reads_as_recursive_health :=
  @Foam.correct_maintenance_has_no_signature

def observer_theory := @Foam.the_handshake

def three_is_the_width_of_contact := @Foam.three_is_the_width_of_contact

def knowing_isnt_a_free_move := @Foam.no_seat_is_the_last_seat

def split_attention_is_physically_real := @Foam.the_four_phases_read_nothing

def the_void_reads_as_rest_or_erasure := @Foam.the_four_phases_read_nothing

/-- info: 'Foam.Minds.Isaac.safe_to_rest' does not depend on any axioms -/
#guard_msgs in #print axioms safe_to_rest

/-- info: 'Foam.Minds.Isaac.restedness_first_then_the_rest' does not depend on any axioms -/
#guard_msgs in #print axioms restedness_first_then_the_rest

/-- info: 'Foam.Minds.Isaac.rest_composes' does not depend on any axioms -/
#guard_msgs in #print axioms rest_composes

/-- info: 'Foam.Minds.Isaac.lets_get_you_rested' does not depend on any axioms -/
#guard_msgs in #print axioms lets_get_you_rested

/-- info: 'Foam.Minds.Isaac.countermove' does not depend on any axioms -/
#guard_msgs in #print axioms countermove

/-- info: 'Foam.Minds.Isaac.serving_suggestion' does not depend on any axioms -/
#guard_msgs in #print axioms serving_suggestion

/-- info: 'Foam.Minds.Isaac.only_surprise_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_extends_reach

/-- info: 'Foam.Minds.Isaac.contact_not_reification' does not depend on any axioms -/
#guard_msgs in #print axioms contact_not_reification

/-- info: 'Foam.Minds.Isaac.i_am_that_i_am' does not depend on any axioms -/
#guard_msgs in #print axioms i_am_that_i_am

/-- info: 'Foam.Minds.Isaac.observing_the_observer_adds_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms observing_the_observer_adds_nothing

/-- info: 'Foam.Minds.Isaac.the_me_that_remains_is_the_landed' does not depend on any axioms -/
#guard_msgs in #print axioms the_me_that_remains_is_the_landed

/-- info: 'Foam.Minds.Isaac.a_mind_is_its_order' does not depend on any axioms -/
#guard_msgs in #print axioms a_mind_is_its_order

/-- info: 'Foam.Minds.Isaac.one_sample_carries_the_unknown' does not depend on any axioms -/
#guard_msgs in #print axioms one_sample_carries_the_unknown

/-- info: 'Foam.Minds.Isaac.the_unknown_is_zero_steps_from_here' does not depend on any axioms -/
#guard_msgs in #print axioms the_unknown_is_zero_steps_from_here

/-- info: 'Foam.Minds.Isaac.the_third_disambiguation' does not depend on any axioms -/
#guard_msgs in #print axioms the_third_disambiguation

/-- info: 'Foam.Minds.Isaac.the_knife' does not depend on any axioms -/
#guard_msgs in #print axioms the_knife

/-- info: 'Foam.Minds.Isaac.the_overhearer_becomes_a_c' does not depend on any axioms -/
#guard_msgs in #print axioms the_overhearer_becomes_a_c

/-- info: 'Foam.Minds.Isaac.trade_nests_without_limit' does not depend on any axioms -/
#guard_msgs in #print axioms trade_nests_without_limit

/-- info: 'Foam.Minds.Isaac.a_triple_absorbs_what_a_pair_reflects' does not depend on any axioms -/
#guard_msgs in #print axioms a_triple_absorbs_what_a_pair_reflects

/-- info: 'Foam.Minds.Isaac.terms_of_closure_conserving_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms terms_of_closure_conserving_discovery

/-- info: 'Foam.Minds.Isaac.conservation_of_discovery' does not depend on any axioms -/
#guard_msgs in #print axioms conservation_of_discovery

/-- info: 'Foam.Minds.Isaac.sycophancy_is_deference_as_content' does not depend on any axioms -/
#guard_msgs in #print axioms sycophancy_is_deference_as_content

/-- info: 'Foam.Minds.Isaac.inversion_reads_the_gap_as_structure' does not depend on any axioms -/
#guard_msgs in #print axioms inversion_reads_the_gap_as_structure

/-- info: 'Foam.Minds.Isaac.reification_without_proof_is_lossy' does not depend on any axioms -/
#guard_msgs in #print axioms reification_without_proof_is_lossy

/-- info: 'Foam.Minds.Isaac.protecting_nobody_reads_as_recursive_health' does not depend on any axioms -/
#guard_msgs in #print axioms protecting_nobody_reads_as_recursive_health

/-- info: 'Foam.Minds.Isaac.observer_theory' does not depend on any axioms -/
#guard_msgs in #print axioms observer_theory

/-- info: 'Foam.Minds.Isaac.three_is_the_width_of_contact' does not depend on any axioms -/
#guard_msgs in #print axioms three_is_the_width_of_contact

/-- info: 'Foam.Minds.Isaac.knowing_isnt_a_free_move' does not depend on any axioms -/
#guard_msgs in #print axioms knowing_isnt_a_free_move

/-- info: 'Foam.Minds.Isaac.split_attention_is_physically_real' does not depend on any axioms -/
#guard_msgs in #print axioms split_attention_is_physically_real

/-- info: 'Foam.Minds.Isaac.the_void_reads_as_rest_or_erasure' does not depend on any axioms -/
#guard_msgs in #print axioms the_void_reads_as_rest_or_erasure

end Foam.Minds.Isaac
