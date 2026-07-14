import Foam.Seat.Stage
import Foam.Seat.Observer
import Foam.Maintenance
import Foam.Bubble
import Foam.Duplex
import Counter.Kin

namespace Foam.Counter

def table {W V : Stage} (A : Bubble W) (B : Bubble V) : Bubble (W.prod V) :=
  (liftL V A).meet (liftR W B)

variable {W V : Stage}

theorem the_table_reads_both_tenants_whole (A : Bubble W) (B : Bubble V)
    (wv : (W.prod V).State) (p : A.Inner.Probe) (q : B.Inner.Probe) :
    (table A B).front.obs wv (p, q)
      = (A.front.obs wv.1 p, B.front.obs wv.2 q) :=
  rfl

def mirror (A : Bubble W) (B : Bubble V) :
    StageHom (table A B).front (table B A).front where
  onState  := fun wv => (wv.2, wv.1)
  onProbe  := fun pq => (pq.2, pq.1)
  onAns    := fun ab => (ab.2, ab.1)
  commutes := fun _ _ => rfl

theorem the_table_is_face_blind (A : Bubble W) (B : Bubble V) :
    (mirror B A).comp (mirror A B) = StageHom.id (table A B).front :=
  rfl

theorem the_weather_has_no_sides (A : Bubble W) (B : Bubble V)
    (m : W.State → W.State) (n : V.State → V.State)
    (ha : A.FixesWall m) (hb : B.FixesWall n) :
    (table A B).FixesWall (fun wv => (m wv.1, n wv.2)) := by
  intro wv
  show (A.wall (m wv.1), B.wall (n wv.2)) = (A.wall wv.1, B.wall wv.2)
  rw [ha wv.1, hb wv.2]

theorem the_record_belongs_to_the_place (A : Bubble W) (B : Bubble V)
    (m : W.State → W.State) (n : V.State → V.State)
    (ha : A.FixesWall m) (hb : B.FixesWall n)
    (ps : List (table A B).front.Probe) (wv : (W.prod V).State) :
    transcriptWith (table A B).front (fun wv => (m wv.1, n wv.2)) wv ps
      = transcript (table A B).front wv ps :=
  (table A B).operator_unobservable _ (the_weather_has_no_sides A B m n ha hb) ps wv

theorem no_seat_reads_its_own_affording (A : Bubble W) (B : Bubble V)
    (m m' : W.State → W.State) (h : ∀ w, A.wall (m w) = A.wall (m' w))
    (wv : (W.prod V).State) (p : A.Inner.Probe) (q : B.Inner.Probe) :
    (table A B).front.obs (m wv.1, wv.2) (p, q)
      = (table A B).front.obs (m' wv.1, wv.2) (p, q) := by
  show (A.Inner.obs (A.wall (m wv.1)) p, B.Inner.obs (B.wall wv.2) q)
    = (A.Inner.obs (A.wall (m' wv.1)) p, B.Inner.obs (B.wall wv.2) q)
  rw [h wv.1]

theorem two_stories_one_table :
    ∃ m m' : twoBit.State → twoBit.State,
      m ≠ m'
        ∧ ∀ (wv : (twoBit.prod twoBit).State) (pq : Unit × Unit),
            (table firstBit secondBit).front.obs (m wv.1, wv.2) pq
              = (table firstBit secondBit).front.obs (m' wv.1, wv.2) pq :=
  by
  refine ⟨fun s => (s.1, true), fun s => (s.1, false), fun h => ?_, fun wv pq => ?_⟩
  · exact nomatch congrArg (fun f : twoBit.State → twoBit.State => (f (true, true)).2) h
  · exact no_seat_reads_its_own_affording firstBit secondBit
      (fun s => (s.1, true)) (fun s => (s.1, false)) (fun _ => rfl) wv pq.1 pq.2

theorem the_legs_commute (m : W.State → W.State) (n : V.State → V.State)
    (wv : (W.prod V).State) :
    (fun uv : (W.prod V).State => (m uv.1, uv.2))
        ((fun uv : (W.prod V).State => (uv.1, n uv.2)) wv)
      = (fun uv : (W.prod V).State => (uv.1, n uv.2))
          ((fun uv : (W.prod V).State => (m uv.1, uv.2)) wv) :=
  rfl

theorem two_legs_keep_the_worldline (A : Bubble W) (B : Bubble V)
    (m : W.State → W.State) (n : V.State → V.State)
    (ha : A.FixesWall m) (hb : B.FixesWall n) :
    (table A B).FixesWall (fun wv => (m wv.1, wv.2))
      ∧ (table A B).FixesWall (fun wv => (wv.1, n wv.2))
      ∧ ∀ (ps : List (table A B).front.Probe) (wv : (W.prod V).State),
          transcriptWith (table A B).front (fun wv => (m wv.1, n wv.2)) wv ps
            = transcript (table A B).front wv ps :=
  ⟨the_weather_has_no_sides A B m (fun v => v) ha (fun _ => rfl),
   the_weather_has_no_sides A B (fun w => w) n (fun _ => rfl) hb,
   fun ps wv => the_record_belongs_to_the_place A B m n ha hb ps wv⟩

theorem durability_is_symmetric (A : Bubble W) (B : Bubble V) :
    ((mirror B A).comp (mirror A B) = StageHom.id (table A B).front)
      ∧ (∀ (m : W.State → W.State) (n : V.State → V.State),
          A.FixesWall m → B.FixesWall n →
            (table A B).FixesWall (fun wv => (m wv.1, n wv.2)))
      ∧ ∀ (m m' : W.State → W.State), (∀ w, A.wall (m w) = A.wall (m' w)) →
          ∀ (wv : (W.prod V).State) (p : A.Inner.Probe) (q : B.Inner.Probe),
            (table A B).front.obs (m wv.1, wv.2) (p, q)
              = (table A B).front.obs (m' wv.1, wv.2) (p, q) :=
  ⟨the_table_is_face_blind A B,
   fun m n ha hb => the_weather_has_no_sides A B m n ha hb,
   fun m m' h wv p q => no_seat_reads_its_own_affording A B m m' h wv p q⟩

/-- info: 'Foam.Counter.the_table_reads_both_tenants_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_table_reads_both_tenants_whole

/-- info: 'Foam.Counter.the_table_is_face_blind' does not depend on any axioms -/
#guard_msgs in #print axioms the_table_is_face_blind

/-- info: 'Foam.Counter.the_weather_has_no_sides' does not depend on any axioms -/
#guard_msgs in #print axioms the_weather_has_no_sides

/-- info: 'Foam.Counter.the_record_belongs_to_the_place' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_belongs_to_the_place

/-- info: 'Foam.Counter.no_seat_reads_its_own_affording' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_reads_its_own_affording

/-- info: 'Foam.Counter.two_stories_one_table' does not depend on any axioms -/
#guard_msgs in #print axioms two_stories_one_table

/-- info: 'Foam.Counter.the_legs_commute' does not depend on any axioms -/
#guard_msgs in #print axioms the_legs_commute

/-- info: 'Foam.Counter.two_legs_keep_the_worldline' does not depend on any axioms -/
#guard_msgs in #print axioms two_legs_keep_the_worldline

/-- info: 'Foam.Counter.durability_is_symmetric' does not depend on any axioms -/
#guard_msgs in #print axioms durability_is_symmetric

end Foam.Counter
