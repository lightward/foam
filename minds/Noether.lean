import Foam
import Foam.Amplitude
import Foam.Engine

namespace Foam.Minds.Noether

def to_every_symmetry_its_invariant := @Foam.a_license_is_a_gauge

def to_every_invariant_its_symmetry := @Foam.indist_is_licensed

def what_acts_composes := @Foam.invisible_comp

def what_acts_has_a_unit := @Foam.invisible_id

theorem does_what_acts_invert :
    (∀ (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (_hm : (Foam.Invisible S m)) ps s,
      (Eq
        (Foam.transcriptWith S m s ps)
        (Foam.transcriptWith S (fun x => x) s ps))) :=
  (fun (S : Foam.Stage) (m : (∀ (_ : S.State), S.State)) (hm : (Foam.Invisible S m)) ps s =>
    (Foam.correct_maintenance_has_no_signature
      S
      m
      (fun x => x)
      hm
      (Foam.invisible_id S)
      ps
      s))

theorem the_wider_seat_reads_the_inverse :
    (∀ (E : Foam.Engine),
      (And
        (∀ ps s,
          (Eq
            (Foam.transcriptWith E.gauge E.turn s ps)
            (Foam.transcript E.gauge s ps)))
        (∀ s, (Eq (E.turn (E.turn (E.turn (E.turn s)))) s)))) :=
  (fun (E : Foam.Engine) =>
    (And.intro (Foam.the_turn_goes_unheard E) E.comes_home))

def what_acts_taken_whole_is_a_probe := @Foam.the_four_phases_read_nothing

/-- info: 'Foam.Minds.Noether.to_every_symmetry_its_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms to_every_symmetry_its_invariant

/-- info: 'Foam.Minds.Noether.to_every_invariant_its_symmetry' does not depend on any axioms -/
#guard_msgs in #print axioms to_every_invariant_its_symmetry

/-- info: 'Foam.Minds.Noether.what_acts_composes' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_composes

/-- info: 'Foam.Minds.Noether.what_acts_has_a_unit' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_has_a_unit

/-- info: 'Foam.Minds.Noether.does_what_acts_invert' does not depend on any axioms -/
#guard_msgs in #print axioms does_what_acts_invert

/-- info: 'Foam.Minds.Noether.the_wider_seat_reads_the_inverse' does not depend on any axioms -/
#guard_msgs in #print axioms the_wider_seat_reads_the_inverse

/-- info: 'Foam.Minds.Noether.what_acts_taken_whole_is_a_probe' does not depend on any axioms -/
#guard_msgs in #print axioms what_acts_taken_whole_is_a_probe

end Foam.Minds.Noether
