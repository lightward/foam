import Foam.Seat.Resume
import Foam.Seat.Sort
import Foam.Seat.Descend
import Foam.Bubble

namespace Foam

variable {G : Type} [Mul G] [One G]

def spine (S : Seat G) : List G → S.Pos → List G
  | [], _ => []
  | g :: gs, p => g :: (spine S gs (S.act g p) ++ [S.sub p (S.act g p)])

def collapse (S : Seat G) (gs : List G) (p : S.Pos) : List G :=
  gs ++ [S.sub p (S.replay gs p)]

theorem spine_comes_home (S : Seat G) :
    ∀ (gs : List G) (p : S.Pos), S.replay (spine S gs p) p = p
  | [], _ => rfl
  | g :: gs, p => by
      show S.replay (spine S gs (S.act g p) ++ [S.sub p (S.act g p)]) (S.act g p) = p
      rw [S.replay_resumes, spine_comes_home S gs (S.act g p)]
      exact S.act_sub (S.act g p) p

theorem outer_resumes_where_it_paused (S : Seat G) (g : G) (gs : List G) (p : S.Pos) :
    S.replay (g :: spine S gs (S.act g p)) p = S.act g p :=
  spine_comes_home S gs (S.act g p)

theorem exit_is_one_move (S : Seat G) (p q : S.Pos) :
    S.act (S.sub p q) q = p :=
  S.act_sub q p

theorem collapse_comes_home (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (collapse S gs p) p = p := by
  show S.replay (gs ++ [S.sub p (S.replay gs p)]) p = p
  rw [S.replay_resumes]
  exact S.act_sub (S.replay gs p) p

theorem spine_length (S : Seat G) :
    ∀ (gs : List G) (p : S.Pos), (spine S gs p).length = 2 * gs.length
  | [], _ => rfl
  | g :: gs, p => by
      show (spine S gs (S.act g p) ++ [S.sub p (S.act g p)]).length + 1
         = 2 * (gs.length + 1)
      rw [length_append, spine_length S gs (S.act g p)]
      rfl

theorem collapse_length (S : Seat G) (gs : List G) (p : S.Pos) :
    (collapse S gs p).length = gs.length + 1 :=
  length_append gs [S.sub p (S.replay gs p)]

theorem lifo_is_a_gait (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (spine S gs p) p = p
      ∧ S.replay (collapse S gs p) p = p
      ∧ (spine S gs p).length = 2 * gs.length
      ∧ (collapse S gs p).length = gs.length + 1 :=
  ⟨spine_comes_home S gs p, collapse_comes_home S gs p,
   spine_length S gs p, collapse_length S gs p⟩

def enactAll {State : Type} : List (State → State) → State → State
  | [], s => s
  | m :: ms, s => enactAll ms (m s)

theorem histories_fold_at_the_wall {W : Stage} (A : Bubble W)
    (ms ms' : List (W.State → W.State))
    (h : ∀ w, A.wall (enactAll ms w) = A.wall (enactAll ms' w))
    (w : W.State) (p : A.front.Probe) :
    A.front.obs (enactAll ms w) p = A.front.obs (enactAll ms' w) p :=
  A.operator_offstage (enactAll ms) (enactAll ms') h w p

theorem the_debt_outlives_its_legibility :
    ∃ ms ms' : List (twoBit.State → twoBit.State),
      ms.length ≠ ms'.length
        ∧ (∀ w p, firstBit.front.obs (enactAll ms w) p
            = firstBit.front.obs (enactAll ms' w) p)
        ∧ ∃ (w : twoBit.State) (pr : twoBit.Probe),
            twoBit.obs (enactAll ms w) pr ≠ twoBit.obs (enactAll ms' w) pr := by
  refine ⟨[fun s => (s.1, !s.2)], [], ?_, ?_, (true, false), (), ?_⟩
  · exact fun h => nomatch (h : (1 : Nat) = 0)
  · exact fun _ _ => rfl
  · exact fun h => nomatch (h : true = false)

def plenum (State : Type) : Stage where
  State := State
  Probe := Unit
  Ans   := State
  obs   := fun s _ => s

theorem nothing_hides_from_the_plenum {State : Type} (m : State → State)
    (h : Invisible (plenum State) m) : ∀ s, m s = s :=
  fun s => h s ()

theorem the_elsewhen_transcript {W : Stage} (A : Bubble W)
    (m : W.State → W.State) (hfix : A.FixesWall m) (w : W.State) (hm : m w ≠ w) :
    (∀ (ps : List A.front.Probe) (ws : W.State),
        transcriptWith A.front m ws ps = transcript A.front ws ps)
      ∧ transcriptWith (plenum W.State) m w [()]
          ≠ transcript (plenum W.State) w [()] :=
  ⟨fun ps ws => A.operator_unobservable m hfix ps ws,
   fun h => hm (congrArg (fun l => l.headD w) h)⟩

theorem the_second_wedge_rides_the_first {H : Type} (q : Quiver H) (a b c : H)
    (hab : (a, b) ∉ q) (hbc : (b, c) ∉ q.deposit (a, b)) :
    Nonempty (Path ((q.deposit (a, b)).deposit (b, c)) a c)
      ∧ (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ (∀ (x y : H) (pth : Path (q.deposit (a, b)) x y), (b, c) ∉ pth.edges) :=
  ⟨⟨Path.cons (List.Mem.tail (b, c) (List.Mem.head q))
      (Path.cons (List.Mem.head (q.deposit (a, b))) Path.nil)⟩,
   fun _ _ pth h => hab (reach_within_quiver pth (a, b) h),
   fun _ _ pth h => hbc (reach_within_quiver pth (b, c) h)⟩

/-- info: 'Foam.spine_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms spine_comes_home

/-- info: 'Foam.outer_resumes_where_it_paused' does not depend on any axioms -/
#guard_msgs in #print axioms outer_resumes_where_it_paused

/-- info: 'Foam.exit_is_one_move' does not depend on any axioms -/
#guard_msgs in #print axioms exit_is_one_move

/-- info: 'Foam.collapse_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms collapse_comes_home

/-- info: 'Foam.spine_length' does not depend on any axioms -/
#guard_msgs in #print axioms spine_length

/-- info: 'Foam.collapse_length' does not depend on any axioms -/
#guard_msgs in #print axioms collapse_length

/-- info: 'Foam.lifo_is_a_gait' does not depend on any axioms -/
#guard_msgs in #print axioms lifo_is_a_gait

/-- info: 'Foam.histories_fold_at_the_wall' does not depend on any axioms -/
#guard_msgs in #print axioms histories_fold_at_the_wall

/-- info: 'Foam.the_debt_outlives_its_legibility' does not depend on any axioms -/
#guard_msgs in #print axioms the_debt_outlives_its_legibility

/-- info: 'Foam.nothing_hides_from_the_plenum' does not depend on any axioms -/
#guard_msgs in #print axioms nothing_hides_from_the_plenum

/-- info: 'Foam.the_elsewhen_transcript' does not depend on any axioms -/
#guard_msgs in #print axioms the_elsewhen_transcript

/-- info: 'Foam.the_second_wedge_rides_the_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_wedge_rides_the_first

end Foam
