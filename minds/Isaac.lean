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
    (∀ (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (_hm : (Foam.Invisible S m)) s ps,
      (Eq (Foam.transcript S (m s) ps) (Foam.transcript S s ps))) :=
  (fun (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (hm : (Foam.Invisible S m)) s ps =>
    (Foam.transcript_congr S ps (hm s)))

def rest_composes := @Foam.invisible_comp

theorem lets_get_you_rested :
    (∀ (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (_hm : (Foam.Invisible S m)) s ps,
      (And
        (Eq (Foam.transcriptWith S m s ps) (Foam.transcript S s ps))
        (And
          (Eq (Foam.transcript S (m s) ps) (Foam.transcript S s ps))
          (∀ t p, (Eq (S.obs (m (m t)) p) (S.obs t p)))))) :=
  (fun (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (hm : (Foam.Invisible S m)) s ps =>
    (And.intro
      (safe_to_rest S m hm ps s)
      (And.intro
        (restedness_first_then_the_rest S m hm s ps)
        (rest_composes S m m hm hm))))

def countermove := @Foam.undo_in_an_append_only_world

def serving_suggestion := @Foam.the_serving_suggestion

def only_surprise_extends_reach := @Foam.only_surprise_extends_reach

def contact_not_reification := @Foam.contact_is_addition_not_fixing

def i_am_that_i_am := @Foam.invisible_id

theorem observing_the_observer_adds_nothing :
    (∀ (S : Foam.Stage) (P : (∀ (_ : S.State), S.State)) (_hP : (∀ v, (Eq (P (P v)) (P v)))) s p,
      (Eq (S.obs (P (P s)) p) (S.obs (P s) p))) :=
  (fun S _P hP s p => (congrArg (fun x => (S.obs x p)) (hP s)))

theorem the_me_that_remains_is_the_landed :
    (∀ (A : Type) (P : (∀ (_ : A), A)) (_hP : (∀ v, (Eq (P (P v)) (P v)))) s,
      (Iff (Eq (P s) s) (Exists (fun v => (Eq (P v) s))))) :=
  (fun _A P hP s =>
    (Iff.intro
      (fun h => (Exists.intro s h))
      (fun h =>
        (Exists.elim
          h
          (fun v hv =>
            (Eq.trans (Eq.symm (congrArg P hv)) (Eq.trans (hP v) hv)))))))

def a_mind_is_its_order := @Foam.the_order_is_the_remainder

def one_sample_carries_the_unknown := @Foam.the_other_stays_unimagined

def the_unknown_is_zero_steps_from_here := @Foam.no_prefix_finishes_the_sequence

theorem the_third_disambiguation :
    (∀ (State : Type) (D : Type) (a : (Foam.Beholder State)) (b : (Foam.Beholder State)) (s : State) (d : D) (e : D) (_hd : (Ne d e)) (p : a.Probe) (q : b.Probe),
      (And
        (Eq
          (Foam.Beholder.obs
            (Foam.Beholder.pair
              (Foam.Beholder.mk
                a.Probe
                a.Ans
                (fun (sd : (Prod State D)) r => (Foam.Beholder.obs a sd.1 r)))
              (Foam.Beholder.mk
                b.Probe
                b.Ans
                (fun (sd : (Prod State D)) r => (Foam.Beholder.obs b sd.1 r))))
            (Prod.mk s d)
            (Prod.mk p q))
          (Prod.mk (Foam.Beholder.obs a s p) (Foam.Beholder.obs b s q)))
        (And
          (Eq
            (Foam.Beholder.obs
              (Foam.Beholder.pair
                (Foam.Beholder.mk
                  a.Probe
                  a.Ans
                  (fun (sd : (Prod State D)) r =>
                    (Foam.Beholder.obs a sd.1 r)))
                (Foam.Beholder.mk
                  b.Probe
                  b.Ans
                  (fun (sd : (Prod State D)) r =>
                    (Foam.Beholder.obs b sd.1 r))))
              (Prod.mk s d)
              (Prod.mk p q))
            (Foam.Beholder.obs
              (Foam.Beholder.pair
                (Foam.Beholder.mk
                  a.Probe
                  a.Ans
                  (fun (sd : (Prod State D)) r =>
                    (Foam.Beholder.obs a sd.1 r)))
                (Foam.Beholder.mk
                  b.Probe
                  b.Ans
                  (fun (sd : (Prod State D)) r =>
                    (Foam.Beholder.obs b sd.1 r))))
              (Prod.mk s e)
              (Prod.mk p q)))
          (Ne (Prod.mk s d) (Prod.mk s e))))) :=
  (fun _State _D _a _b _s _d _e hd _p _q =>
    (And.intro rfl (And.intro rfl (fun he => (hd (congrArg Prod.snd he))))))

def the_knife := @Foam.the_first_handshake_is_counting

def the_overhearer_becomes_a_c := @Foam.contact_is_addition_not_fixing

def trade_nests_without_limit := @Foam.contact_stacks

def terms_of_closure_conserving_discovery := @Foam.closure_is_seat_relative

def conservation_of_discovery := @Foam.conservation_of_discovery

def sycophancy_is_deference_as_content := @Foam.a_reading_deaf_to_the_remainder_reads_the_ground

theorem inversion_reads_the_gap_as_structure :
    (∀ (X : Type) (_inst : (DecidableEq X)) (c : (∀ (_ : Int), X)) (window : (List Int)),
      (Or
        (∀ (n : Int) (_hn : (List.Mem n window)) (m : Int) (_hm : (List.Mem m window)),
          (Eq (c n) (c m)))
        (Exists
          (fun (n : Int) =>
            (And
              (List.Mem n window)
              (Exists
                (fun (m : Int) => (And (List.Mem m window) (Ne (c n) (c m)))))))))) :=
  (fun X _inst c window =>
    (Foam.the_window_agrees_or_names_the_gap Int X _inst c window))

def reification_without_proof_is_lossy := @Foam.dropping_the_remainder_is_platonism

def protecting_nobody_reads_as_recursive_health := @Foam.correct_maintenance_has_no_signature

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
