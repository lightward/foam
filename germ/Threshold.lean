import Rest
import Witness
open Room Face Rest Witness

namespace Threshold

universe u v w u' v' w' u''

def threshold (F : Face) (seats : List (List F.Probe)) {I : Type u'} {O : Type v'} (R : Runner.{u', v', w'} I O)
    (s : R.m.S) : Prop :=
  covers F seats ∧ R.rest s = true

def thresholdAt (F : Face) (ps : List F.Probe) (seats : List (List F.Probe)) {I : Type u'} {O : Type v'}
    (R : Runner.{u', v', w'} I O) (s : R.m.S) : Prop :=
  coversAll F ps seats ∧ R.rest s = true

theorem the_crossing_is_licensed (F : Face) {seats : List (List F.Probe)} {x y : F.State}
    (hc : covers F seats) (hw : witnessed F seats x y) {W : Type v'} (w w' : W) :
    alike (host F W) (atTheDoor x w) (atTheDoor y w') := sorry

theorem the_threshold {I : Type u'} (F : Face.{u, v, w}) (seats : List (List F.Probe))
    (R : Runner.{u', u, w'} I F.State) (s : R.m.S) (t : threshold F seats R s)
    {W : Type u} (w w' : W) (sl : List F.Probe) :
    alike (host F W) (atTheDoor (R.m.out s) w) (atTheDoor (R.m.out s) w')
      ∧ reads (host F W) sl (atTheDoor (R.m.out s) w) = reads F sl (R.m.out s)
      ∧ (∀ y, witnessed F seats (R.m.out s) y → alike F (R.m.out s) y)
      ∧ runs R.m R.steer R.rest s 0 = some (R.m.out s) :=
  ⟨the_host_merges_the_guests F W (R.m.out s) w w',
    (by (apply Witness.the_word_at_the_door_is_unread_at_every_seat <;> assumption)), fun _ hw =>
    (by
      (apply Witness.forever_hold_your_peace <;>
          first
          | (apply ((t)).1 <;> fail)
          | assumption)),
    by
    show cond (R.rest s) (some (R.m.out s)) none = some (R.m.out s)
    rw [t.2]
    rfl⟩

theorem the_route_is_shed {I : Type u} {O : Type v} (R : Runner.{u, v, u} I O) :
    alike (haltingGap.{u, v, u} I O) R (replayRunner R) := sorry

theorem the_crossing_is_licensed_at_the_room (F : Face) (ps : List F.Probe) {seats : List (List F.Probe)}
    {x y : F.State} (hc : coversAll F ps seats) (hw : witnessed F seats x y) {W : Type v'} (w w' : W) :
    reads (host F W) ps (atTheDoor x w) = reads (host F W) ps (atTheDoor y w') := sorry

theorem the_threshold_at_the_room {I : Type u'} (F : Face.{u, v, w}) (ps : List F.Probe) (seats : List (List F.Probe))
    (R : Runner.{u', u, w'} I F.State) (s : R.m.S) (t : thresholdAt F ps seats R s)
    {W : Type u} (w w' : W) (sl : List F.Probe) :
    alike (host F W) (atTheDoor (R.m.out s) w) (atTheDoor (R.m.out s) w')
      ∧ reads (host F W) sl (atTheDoor (R.m.out s) w) = reads F sl (R.m.out s)
      ∧ (∀ y, witnessed F seats (R.m.out s) y → reads F ps (R.m.out s) = reads F ps y)
      ∧ runs R.m R.steer R.rest s 0 = some (R.m.out s) := sorry

theorem a_threshold_is_a_threshold_at_every_room (F : Face) (ps : List F.Probe) (seats : List (List F.Probe))
    {I : Type u'} {O : Type v'} (R : Runner.{u', v', w'} I O) (s : R.m.S) (t : threshold F seats R s) :
    thresholdAt F ps seats R s := sorry

end Threshold
