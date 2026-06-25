import Foam.Seat.Rendezvous

namespace Foam

theorem superposition (f : Field) (a b : Int) (hab : a ≠ b) :
    indist reader.dress.obs (f, a) (f, b) ∧ (f, a) ≠ (f, b) :=
  ⟨fun _ => rfl, fun h => hab (congrArg Prod.snd h)⟩

theorem field_cannot_close (f : Field) (a b : Int) :
    ¬ ∃ p, reader.dress.obs (f, a) p ≠ reader.dress.obs (f, b) p :=
  fun ⟨_, hp⟩ => hp rfl

def bAck (f : Field) : Field := writeB (reader.obs f probeA) f

theorem one_round (x : Fiber) (f : Field) :
    reader.obs (bAck (writeA x f)) probeB = x := rfl

def ackSeam : Seam (List Fiber) (CoList Fiber) := playbackSeam f0

def commonKnowledge : CoList Fiber := forever f0

theorem ack_faithful {l l' : List Fiber} (h : ackSeam.up l = ackSeam.up l') : l = l' :=
  ackSeam.faithful h

theorem ack_no_common_knowledge :
    ¬ ∃ g : CoList Fiber → List Fiber, ∀ c, ackSeam.up (g c) = c :=
  ackSeam.no_section

theorem zeno_short (l : List Fiber) :
    ∃ n, (playback l).at_ n ≠ commonKnowledge.at_ n :=
  forever_escapes f0 l

theorem measurement (f : Field) (a b : Int) (hab : a ≠ b) :
    (indist reader.dress.obs (f, a) (f, b) ∧ (f, a) ≠ (f, b))
      ∧ (¬ ∃ p, reader.dress.obs (f, a) p ≠ reader.dress.obs (f, b) p)
      ∧ (¬ ∃ g : CoList Fiber → List Fiber, ∀ c, ackSeam.up (g c) = c) :=
  ⟨superposition f a b hab, field_cannot_close f a b, ackSeam.no_section⟩

/-- info: 'Foam.superposition' does not depend on any axioms -/
#guard_msgs in #print axioms superposition

/-- info: 'Foam.field_cannot_close' does not depend on any axioms -/
#guard_msgs in #print axioms field_cannot_close

/-- info: 'Foam.one_round' does not depend on any axioms -/
#guard_msgs in #print axioms one_round

/-- info: 'Foam.ack_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms ack_faithful

/-- info: 'Foam.ack_no_common_knowledge' does not depend on any axioms -/
#guard_msgs in #print axioms ack_no_common_knowledge

/-- info: 'Foam.zeno_short' does not depend on any axioms -/
#guard_msgs in #print axioms zeno_short

/-- info: 'Foam.measurement' does not depend on any axioms -/
#guard_msgs in #print axioms measurement

end Foam
