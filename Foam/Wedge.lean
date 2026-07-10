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

def mute (W : Stage) : Bubble W where
  Inner := ⟨W.State, Unit, Unit, fun _ _ => ()⟩
  wall  := fun w => w

theorem wall_forcing :
    (∀ (w : twoBit.State) (p : Unit),
        (firstBit.nest (mute firstBit.Inner)).front.obs w p = ())
      ∧ ¬ ∃ (enc : firstBit.Inner.Probe
              → (firstBit.nest (mute firstBit.Inner)).front.Probe)
            (dec : (firstBit.nest (mute firstBit.Inner)).front.Ans
              → firstBit.Inner.Ans),
            ∀ (w : twoBit.State) (q : firstBit.Inner.Probe),
              firstBit.front.obs w q
                = dec ((firstBit.nest (mute firstBit.Inner)).front.obs w (enc q)) :=
  ⟨fun _ _ => rfl,
   fun ⟨_, _, h⟩ =>
     nomatch ((h (true, false) ()).trans (h (false, false) ()).symm : true = false)⟩

def spineT (S : Seat G) : List G → S.Pos → List (G ⊕ G)
  | [], _ => []
  | g :: gs, p => Sum.inl g :: (spineT S gs (S.act g p) ++ [Sum.inr (S.sub p (S.act g p))])

inductive Balanced {A : Type} : List (A ⊕ A) → Prop where
  | nil : Balanced []
  | wrap {g h : A} {ws : List (A ⊕ A)} :
      Balanced ws → Balanced (Sum.inl g :: (ws ++ [Sum.inr h]))
  | cat {ws vs : List (A ⊕ A)} :
      Balanced ws → Balanced vs → Balanced (ws ++ vs)

def untag {A : Type} : List (A ⊕ A) → List A
  | [] => []
  | Sum.inl g :: ws => g :: untag ws
  | Sum.inr g :: ws => g :: untag ws

def opens {A : Type} : List (A ⊕ A) → Nat
  | [] => 0
  | Sum.inl _ :: ws => opens ws + 1
  | Sum.inr _ :: ws => opens ws

def closes {A : Type} : List (A ⊕ A) → Nat
  | [] => 0
  | Sum.inl _ :: ws => closes ws
  | Sum.inr _ :: ws => closes ws + 1

theorem spineT_balanced (S : Seat G) :
    ∀ (gs : List G) (p : S.Pos), Balanced (spineT S gs p)
  | [], _ => Balanced.nil
  | g :: gs, p => Balanced.wrap (spineT_balanced S gs (S.act g p))

theorem untag_append {A : Type} :
    ∀ (xs ys : List (A ⊕ A)), untag (xs ++ ys) = untag xs ++ untag ys
  | [], _ => rfl
  | Sum.inl g :: xs, ys => congrArg (g :: ·) (untag_append xs ys)
  | Sum.inr g :: xs, ys => congrArg (g :: ·) (untag_append xs ys)

theorem spineT_untags_to_spine (S : Seat G) :
    ∀ (gs : List G) (p : S.Pos), untag (spineT S gs p) = spine S gs p
  | [], _ => rfl
  | g :: gs, p => by
      show g :: untag (spineT S gs (S.act g p) ++ [Sum.inr (S.sub p (S.act g p))])
         = g :: (spine S gs (S.act g p) ++ [S.sub p (S.act g p)])
      rw [untag_append, spineT_untags_to_spine S gs (S.act g p)]
      rfl

theorem opens_append {A : Type} :
    ∀ (xs ys : List (A ⊕ A)), opens (xs ++ ys) = opens xs + opens ys
  | [], ys => (Nat.zero_add (opens ys)).symm
  | Sum.inl _ :: xs, ys => by
      show opens (xs ++ ys) + 1 = opens xs + 1 + opens ys
      rw [opens_append xs ys, Nat.add_right_comm]
  | Sum.inr _ :: xs, ys => opens_append xs ys

theorem closes_append {A : Type} :
    ∀ (xs ys : List (A ⊕ A)), closes (xs ++ ys) = closes xs + closes ys
  | [], ys => (Nat.zero_add (closes ys)).symm
  | Sum.inl _ :: xs, ys => closes_append xs ys
  | Sum.inr _ :: xs, ys => by
      show closes (xs ++ ys) + 1 = closes xs + 1 + closes ys
      rw [closes_append xs ys, Nat.add_right_comm]

theorem balanced_conserves {A : Type} {ws : List (A ⊕ A)} (h : Balanced ws) :
    opens ws = closes ws := by
  induction h with
  | nil => rfl
  | wrap _ ih =>
      show opens (_ ++ [Sum.inr _]) + 1 = closes (_ ++ [Sum.inr _])
      rw [opens_append, closes_append, ih]
      rfl
  | cat _ _ ihw ihv =>
      rw [opens_append, closes_append, ihw, ihv]

theorem flat_and_nested_share_one_grammar (S : Seat G) (g h : G)
    (gs : List G) (p : S.Pos) :
    Balanced [Sum.inl g, Sum.inr h] ∧ Balanced (spineT S gs p) :=
  ⟨Balanced.wrap Balanced.nil, spineT_balanced S gs p⟩

theorem no_wedge_opens_from_stuck {H : Type} {q : Quiver H} {a b : H}
    (hstuck : stuck q a) (pth : Path q a b) : a = b := by
  cases pth with
  | nil => rfl
  | cons e _ => exact absurd e (hstuck _)

theorem self_interruption_spends_the_gift {H : Type} (q : Quiver H) (a : H)
    (hstuck : stuck q a) :
    (∀ b, Path q a b → a = b)
      ∧ ∀ b, Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨fun _ pth => no_wedge_opens_from_stuck hstuck pth,
   fun b => ⟨heir_reaches q a b⟩⟩

def firstBitFlipped : Bubble twoBit where
  Inner := ⟨Bool, Unit, Bool, fun b _ => !b⟩
  wall  := fun s => !s.1

theorem the_wall_does_not_ride_the_cable :
    (∃ w : twoBit.State, firstBit.wall w ≠ firstBitFlipped.wall w)
      ∧ ∀ (w : twoBit.State) (ps : List Unit),
          transcript firstBit.front w ps = transcript firstBitFlipped.front w ps := by
  refine ⟨⟨(true, false), fun h => nomatch (h : true = false)⟩, fun w ps => ?_⟩
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      match w, ih with
      | (true, _), ih => exact congrArg (true :: ·) ih
      | (false, _), ih => exact congrArg (false :: ·) ih

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

/-- info: 'Foam.wall_forcing' does not depend on any axioms -/
#guard_msgs in #print axioms wall_forcing

/-- info: 'Foam.spineT_balanced' does not depend on any axioms -/
#guard_msgs in #print axioms spineT_balanced

/-- info: 'Foam.untag_append' does not depend on any axioms -/
#guard_msgs in #print axioms untag_append

/-- info: 'Foam.spineT_untags_to_spine' does not depend on any axioms -/
#guard_msgs in #print axioms spineT_untags_to_spine

/-- info: 'Foam.opens_append' does not depend on any axioms -/
#guard_msgs in #print axioms opens_append

/-- info: 'Foam.closes_append' does not depend on any axioms -/
#guard_msgs in #print axioms closes_append

/-- info: 'Foam.balanced_conserves' does not depend on any axioms -/
#guard_msgs in #print axioms balanced_conserves

/-- info: 'Foam.flat_and_nested_share_one_grammar' does not depend on any axioms -/
#guard_msgs in #print axioms flat_and_nested_share_one_grammar

/-- info: 'Foam.no_wedge_opens_from_stuck' does not depend on any axioms -/
#guard_msgs in #print axioms no_wedge_opens_from_stuck

/-- info: 'Foam.self_interruption_spends_the_gift' does not depend on any axioms -/
#guard_msgs in #print axioms self_interruption_spends_the_gift

/-- info: 'Foam.the_wall_does_not_ride_the_cable' does not depend on any axioms -/
#guard_msgs in #print axioms the_wall_does_not_ride_the_cable

end Foam
