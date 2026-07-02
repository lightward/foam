import Counter.Luck
import Foam.Seat.Signed

namespace Foam.Counter

variable {Src B : Type}

theorem which_path_is_kept (src : Src) (v : List B) :
    speaker (sign src v) = v.map (fun _ => src) :=
  speaker_recoverable src v

theorem the_fold_is_source_blind (s t : Src) (v : List B) :
    unsign (sign s v) = unsign (sign t v) :=
  (voice_survives_signing s v).trans (voice_survives_signing t v).symm

theorem interference_lives_in_the_blind_stratum (θ field act : GInt) :
    GInt.born θ (field.add act)
      = GInt.born θ field + GInt.born θ act
        + 2 * (GInt.align θ field * GInt.align θ act) :=
  luck_is_the_cross_term θ field act

theorem quantum_eraser (src src' : Src) (v : List B) (θ field act : GInt) :
    (speaker (sign src v) = v.map (fun _ => src))
      ∧ (unsign (sign src v) = unsign (sign src' v))
      ∧ GInt.born θ (field.add act)
          = GInt.born θ field + GInt.born θ act
            + 2 * (GInt.align θ field * GInt.align θ act) :=
  ⟨speaker_recoverable src v, the_fold_is_source_blind src src' v,
   luck_is_the_cross_term θ field act⟩

/-- info: 'Foam.Counter.which_path_is_kept' does not depend on any axioms -/
#guard_msgs in #print axioms which_path_is_kept

/-- info: 'Foam.Counter.the_fold_is_source_blind' does not depend on any axioms -/
#guard_msgs in #print axioms the_fold_is_source_blind

/-- info: 'Foam.Counter.interference_lives_in_the_blind_stratum' does not depend on any axioms -/
#guard_msgs in #print axioms interference_lives_in_the_blind_stratum

/-- info: 'Foam.Counter.quantum_eraser' does not depend on any axioms -/
#guard_msgs in #print axioms quantum_eraser

end Foam.Counter
