import Foam.Bubble
import Foam.Seat.Tight
import Foam.Seat.Summit

namespace Foam

def Resolver (c : Nat → Nat) (n : Nat) : Prop := ∀ m, n ≤ m → c m = c n

theorem resolver_is_seated (c : Nat → Nat) (n : Nat) : Resolver c n ↔ Seated c n :=
  Iff.rfl

theorem resolver_reps_change_nothing (c : Nat → Nat) (n : Nat) :
    Resolver c n ↔ ∀ m, n ≤ m → Rests c m :=
  seated_iff_rests_forever

def census {A : Type u} (l : List A) : Nat := l.length

def seat {A : Type u} : (l : List A) → Fin l.length → A
  | a :: _, ⟨0, _⟩ => a
  | _ :: l, ⟨i + 1, h⟩ => seat l ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem census_map {A : Type u} {B : Type v} (f : A → B) :
    ∀ l : List A, census (l.map f) = census l
  | [] => rfl
  | _ :: l => congrArg (· + 1) (census_map f l)

def Beholder.quiet (State : Type) : Beholder State where
  Probe := Unit
  Ans   := Unit
  obs   := fun _ _ => ()

def Beholder.fold {State : Type} : List (Beholder State) → Beholder State
  | [] => Beholder.quiet State
  | b :: bs => b.pair (Beholder.fold bs)

def seatProbe {State : Type} : (bs : List (Beholder State)) → (i : Fin bs.length) →
    (Beholder.fold bs).Probe → (seat bs i).Probe
  | _ :: _, ⟨0, _⟩, q => q.1
  | _ :: bs, ⟨i + 1, h⟩, q => seatProbe bs ⟨i, Nat.lt_of_succ_lt_succ h⟩ q.2

def seatAns {State : Type} : (bs : List (Beholder State)) → (i : Fin bs.length) →
    (Beholder.fold bs).Ans → (seat bs i).Ans
  | _ :: _, ⟨0, _⟩, a => a.1
  | _ :: bs, ⟨i + 1, h⟩, a => seatAns bs ⟨i, Nat.lt_of_succ_lt_succ h⟩ a.2

theorem fold_reads_every_seat {State : Type} :
    ∀ (bs : List (Beholder State)) (i : Fin bs.length) (s : State)
      (q : (Beholder.fold bs).Probe),
      seatAns bs i ((Beholder.fold bs).obs s q) = (seat bs i).obs s (seatProbe bs i q)
  | _ :: _, ⟨0, _⟩, _, _ => rfl
  | _ :: bs, ⟨i + 1, h⟩, s, q =>
      fold_reads_every_seat bs ⟨i, Nat.lt_of_succ_lt_succ h⟩ s q.2

def splice {State : Type} : (bs : List (Beholder State)) → (i : Fin bs.length) →
    (seat bs i).Probe → (Beholder.fold bs).Probe → (Beholder.fold bs).Probe
  | _ :: _, ⟨0, _⟩, p, q => (p, q.2)
  | _ :: bs, ⟨i + 1, h⟩, p, q => (q.1, splice bs ⟨i, Nat.lt_of_succ_lt_succ h⟩ p q.2)

theorem splice_asks_the_seat {State : Type} :
    ∀ (bs : List (Beholder State)) (i : Fin bs.length)
      (p : (seat bs i).Probe) (q : (Beholder.fold bs).Probe),
      seatProbe bs i (splice bs i p q) = p
  | _ :: _, ⟨0, _⟩, _, _ => rfl
  | _ :: bs, ⟨i + 1, h⟩, p, q =>
      splice_asks_the_seat bs ⟨i, Nat.lt_of_succ_lt_succ h⟩ p q.2

theorem splice_keeps_the_rest {State : Type} :
    ∀ (bs : List (Beholder State)) (i j : Fin bs.length), i.val ≠ j.val →
      ∀ (p : (seat bs i).Probe) (q : (Beholder.fold bs).Probe),
      seatProbe bs j (splice bs i p q) = seatProbe bs j q
  | _ :: _, ⟨0, _⟩, ⟨0, _⟩, hne, _, _ => absurd rfl hne
  | _ :: _, ⟨0, _⟩, ⟨_ + 1, _⟩, _, _, _ => rfl
  | _ :: _, ⟨_ + 1, _⟩, ⟨0, _⟩, _, _, _ => rfl
  | _ :: bs, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hne, p, q =>
      splice_keeps_the_rest bs ⟨i, Nat.lt_of_succ_lt_succ hi⟩
        ⟨j, Nat.lt_of_succ_lt_succ hj⟩ (fun e => hne (congrArg Nat.succ e)) p q.2

theorem starving_seat_starves_the_fold {State : Type} (bs : List (Beholder State))
    (i : Fin bs.length) (h : (seat bs i).Probe → False) :
    (Beholder.fold bs).Probe → False :=
  fun q => h (seatProbe bs i q)

def house {State P A : Type} (os : List (State → P → A)) : Beholder State where
  Probe := P
  Ans   := List A
  obs   := fun s p => os.map (fun o => o s p)

theorem house_headcount {State P A : Type} (os : List (State → P → A))
    (s : State) (p : P) : ((house os).obs s p).length = census os :=
  show (os.map (fun o => o s p)).length = os.length from
    length_map (fun o => o s p) os

theorem house_hears_everyone {State P A : Type} (os : List (State → P → A))
    (s : State) (p : P) {o : State → P → A} (h : o ∈ os) :
    List.Mem (o s p) ((house os).obs s p) :=
  mem_map_of_mem (fun o => o s p) h

def rosterRead {State P A : Type} : List (State → P → A) → Nat → State → P → Option A
  | [], _, _, _ => none
  | o :: _, 0, s, p => some (o s p)
  | _ :: os, i + 1, s, p => rosterRead os i s p

def roster {State P A : Type} (os : List (State → P → A)) : Stage where
  State := State
  Probe := Nat × P
  Ans   := Option A
  obs   := fun s ip => rosterRead os ip.1 s ip.2

def rollFrom {P : Type} (p : P) : Nat → Nat → List (Nat × P)
  | _, 0 => []
  | k, n + 1 => (k, p) :: rollFrom p (k + 1) n

def rollCall {P : Type} (p : P) (n : Nat) : List (Nat × P) := rollFrom p 0 n

theorem rollFrom_length {P : Type} (p : P) :
    ∀ (n k : Nat), (rollFrom p k n).length = n
  | 0, _ => rfl
  | n + 1, k => congrArg (· + 1) (rollFrom_length p n (k + 1))

theorem transcript_length (S : Stage) (s : S.State) :
    ∀ ps : List S.Probe, (transcript S s ps).length = ps.length
  | [] => rfl
  | _ :: ps => congrArg (· + 1) (transcript_length S s ps)

theorem roster_shift {State P A : Type} (o : State → P → A)
    (os : List (State → P → A)) (s : State) (p : P) :
    ∀ (n k : Nat),
      transcript (roster (o :: os)) s (rollFrom p (k + 1) n)
        = transcript (roster os) s (rollFrom p k n)
  | 0, _ => rfl
  | n + 1, k =>
      congrArg (rosterRead os k s p :: ·) (roster_shift o os s p n (k + 1))

theorem roster_answers_the_house {State P A : Type} (s : State) (p : P) :
    ∀ os : List (State → P → A),
      transcript (roster os) s (rollCall p (census os))
        = ((house os).obs s p).map some
  | [] => rfl
  | o :: os =>
      congrArg (some (o s p) :: ·)
        ((roster_shift o os s p (census os) 0).trans (roster_answers_the_house s p os))

theorem census_conserved {State P A : Type} (os : List (State → P → A))
    (s : State) (p : P) :
    (transcript (roster os) s (rollCall p (census os))).length = census os
      ∧ (transcript (house os).toStage s [p]).length = 1
      ∧ ((house os).obs s p).length = census os :=
  ⟨(transcript_length (roster os) s (rollCall p (census os))).trans
      (rollFrom_length p (census os) 0),
   rfl, house_headcount os s p⟩

def Bubble.quiet (W : Stage) : Bubble W where
  Inner := ⟨Unit, Unit, Unit, fun _ _ => ()⟩
  wall  := fun _ => ()

def Bubble.meetAll {W : Stage} : List (Bubble W) → Bubble W
  | [] => Bubble.quiet W
  | A :: As => A.meet (Bubble.meetAll As)

theorem meetAll_wall_is_fold {W : Stage} :
    ∀ As : List (Bubble W),
      (Bubble.meetAll As).front.behold
        = Beholder.fold (As.map fun A => A.front.behold)
  | [] => rfl
  | A :: As => congrArg (A.front.behold.pair ·) (meetAll_wall_is_fold As)

def wallHom {W : Stage} : (As : List (Bubble W)) → (i : Fin As.length) →
    StageHom (Bubble.meetAll As).front ((seat As i).front)
  | _ :: _, ⟨0, _⟩ =>
      { onState := fun w => w, onProbe := fun q => q.1, onAns := fun a => a.1,
        commutes := fun _ _ => rfl }
  | _ :: As, ⟨i + 1, h⟩ =>
      (wallHom As ⟨i, Nat.lt_of_succ_lt_succ h⟩).comp
        { onState := fun w => w, onProbe := fun q => q.2, onAns := fun a => a.2,
          commutes := fun _ _ => rfl }

theorem every_seat_reads_through_the_wall {W : Stage} (As : List (Bubble W))
    (i : Fin As.length) (w : W.State) (q : (Bubble.meetAll As).front.Probe) :
    (seat As i).front.obs ((wallHom As i).onState w) ((wallHom As i).onProbe q)
      = (wallHom As i).onAns ((Bubble.meetAll As).front.obs w q) :=
  (wallHom As i).commutes w q

theorem every_bubble_still_present {W : Stage} (As : List (Bubble W))
    (i : Fin As.length) :
    Nonempty (StageHom (Bubble.meetAll As).front ((seat As i).front)) :=
  ⟨wallHom As i⟩

/-- info: 'Foam.resolver_is_seated' does not depend on any axioms -/
#guard_msgs in #print axioms resolver_is_seated

/-- info: 'Foam.resolver_reps_change_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms resolver_reps_change_nothing

/-- info: 'Foam.census_map' does not depend on any axioms -/
#guard_msgs in #print axioms census_map

/-- info: 'Foam.fold_reads_every_seat' does not depend on any axioms -/
#guard_msgs in #print axioms fold_reads_every_seat

/-- info: 'Foam.splice_asks_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms splice_asks_the_seat

/-- info: 'Foam.splice_keeps_the_rest' does not depend on any axioms -/
#guard_msgs in #print axioms splice_keeps_the_rest

/-- info: 'Foam.starving_seat_starves_the_fold' does not depend on any axioms -/
#guard_msgs in #print axioms starving_seat_starves_the_fold

/-- info: 'Foam.house_headcount' does not depend on any axioms -/
#guard_msgs in #print axioms house_headcount

/-- info: 'Foam.house_hears_everyone' does not depend on any axioms -/
#guard_msgs in #print axioms house_hears_everyone

/-- info: 'Foam.rollFrom_length' does not depend on any axioms -/
#guard_msgs in #print axioms rollFrom_length

/-- info: 'Foam.transcript_length' does not depend on any axioms -/
#guard_msgs in #print axioms transcript_length

/-- info: 'Foam.roster_shift' does not depend on any axioms -/
#guard_msgs in #print axioms roster_shift

/-- info: 'Foam.roster_answers_the_house' does not depend on any axioms -/
#guard_msgs in #print axioms roster_answers_the_house

/-- info: 'Foam.census_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms census_conserved

/-- info: 'Foam.meetAll_wall_is_fold' does not depend on any axioms -/
#guard_msgs in #print axioms meetAll_wall_is_fold

/-- info: 'Foam.every_seat_reads_through_the_wall' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_reads_through_the_wall

/-- info: 'Foam.every_bubble_still_present' does not depend on any axioms -/
#guard_msgs in #print axioms every_bubble_still_present

end Foam
