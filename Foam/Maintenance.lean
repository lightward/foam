import Foam.Scar
import Foam.Seat.Stage

namespace Foam

def Invisible (S : Stage) (m : S.State → S.State) : Prop :=
  ∀ s p, S.obs (m s) p = S.obs s p

theorem invisible_id (S : Stage) : Invisible S (fun s => s) := fun _ _ => rfl

theorem invisible_comp (S : Stage) (m n : S.State → S.State)
    (hm : Invisible S m) (hn : Invisible S n) : Invisible S (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

def transcript (S : Stage) (s : S.State) : List S.Probe → List S.Ans
  | [] => []
  | p :: ps => S.obs s p :: transcript S s ps

def transcriptWith (S : Stage) (m : S.State → S.State) :
    S.State → List S.Probe → List S.Ans
  | _, [] => []
  | s, p :: ps => S.obs (m s) p :: transcriptWith S m (m s) ps

theorem transcript_congr (S : Stage) (ps : List S.Probe) :
    ∀ {t s : S.State}, (∀ p, S.obs t p = S.obs s p) →
      transcript S t ps = transcript S s ps := by
  induction ps with
  | nil => intro t s _; rfl
  | cons p ps ih =>
    intro t s h
    show S.obs t p :: transcript S t ps = S.obs s p :: transcript S s ps
    rw [h p, ih h]

theorem maintenance_unobservable (S : Stage) (m : S.State → S.State)
    (h : Invisible S m) (ps : List S.Probe) :
    ∀ s, transcriptWith S m s ps = transcript S s ps := by
  induction ps with
  | nil => intro s; rfl
  | cons p ps ih =>
    intro s
    show S.obs (m s) p :: transcriptWith S m (m s) ps = S.obs s p :: transcript S s ps
    rw [h s p, ih (m s), transcript_congr S ps (h s)]

def posPart : Int → Nat
  | Int.ofNat m => m
  | Int.negSucc _ => 0

theorem settle_invisible : ∀ b : Int, posPart (checkedSettle b b) = posPart b
  | Int.ofNat _ => rfl
  | Int.negSucc 0 => rfl
  | Int.negSucc (_ + 1) => rfl

theorem drain_visible : ∃ b : Int, posPart (checkedDrain b b) ≠ posPart b :=
  ⟨1, fun h => Nat.noConfusion h⟩

def BalanceStage : Stage := ⟨Int, Unit, Nat, fun b _ => posPart b⟩

theorem settle_invisible' : Invisible BalanceStage (fun b => checkedSettle b b) :=
  fun b _ => settle_invisible b

/-- info: 'Foam.invisible_comp' does not depend on any axioms -/
#guard_msgs in #print axioms invisible_comp

/-- info: 'Foam.transcript_congr' does not depend on any axioms -/
#guard_msgs in #print axioms transcript_congr

/-- info: 'Foam.maintenance_unobservable' does not depend on any axioms -/
#guard_msgs in #print axioms maintenance_unobservable

/-- info: 'Foam.settle_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms settle_invisible

/-- info: 'Foam.drain_visible' does not depend on any axioms -/
#guard_msgs in #print axioms drain_visible

/-- info: 'Foam.settle_invisible'' does not depend on any axioms -/
#guard_msgs in #print axioms settle_invisible'

end Foam
