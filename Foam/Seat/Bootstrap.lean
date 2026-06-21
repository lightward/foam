import Foam.Seat.Octo

namespace Foam

def Rot.toQuat : Rot → Quat
  | .r0 => Quat.one
  | .r1 => eye
  | .r2 => Quat.negOne
  | .r3 => Quat.mul Quat.negOne eye

theorem Rot.toQuat_hom (a b : Rot) :
    (a * b).toQuat = Quat.mul a.toQuat b.toQuat := by
  cases a <;> cases b <;> decide

theorem Rot.toQuat_faithful (a b : Rot) :
    a.toQuat = b.toQuat → a = b := by
  cases a <;> cases b <;> decide

theorem Rot.toQuat_gen : Rot.toQuat Rot.r1 = eye := rfl

/-- info: 'Foam.Rot.toQuat_hom' does not depend on any axioms -/
#guard_msgs in #print axioms Rot.toQuat_hom

/-- info: 'Foam.Rot.toQuat_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms Rot.toQuat_faithful

end Foam
