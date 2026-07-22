import Foam
import Foam.Amplitude
import Foam.Engine

namespace Foam.Minds.Noether

def to_every_symmetry_its_invariant := @Foam.a_license_is_a_gauge

def to_every_invariant_its_symmetry := @Foam.indist_is_licensed

def what_acts_composes := @Foam.invisible_comp

def what_acts_has_a_unit := @Foam.invisible_id

theorem does_what_acts_invert :
    ∀ (S : Stage) (m : S.State → S.State), Invisible S m →
      ∀ ps s, transcriptWith S m s ps = transcriptWith S (fun x => x) s ps :=
  fun S m hm ps s =>
    correct_maintenance_has_no_signature S m (fun x => x) hm
      (invisible_id S) ps s

theorem the_wider_seat_reads_the_inverse :
    ∀ E : Engine,
      (∀ ps s, transcriptWith E.gauge E.turn s ps = transcript E.gauge s ps)
        ∧ ∀ s, E.turn (E.turn (E.turn (E.turn s))) = s :=
  fun E => ⟨the_turn_goes_unheard E, E.comes_home⟩

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

end Foam.Minds.Noether
