import Foam.Seat.Closure

namespace Foam

def Ascends (c : Nat → Nat) : Prop := ∀ n, c n ≤ c (n + 1)

def Climbs (c : Nat → Nat) : Prop := ∀ n, c n < c (n + 1)

def Rests (c : Nat → Nat) (n : Nat) : Prop := c (n + 1) = c n

def Seated (c : Nat → Nat) (n : Nat) : Prop := ∀ m, n ≤ m → c m = c n

theorem ascends_le_add {c : Nat → Nat} (h : Ascends c) :
    ∀ (a k : Nat), c a ≤ c (a + k)
  | _, 0 => Nat.le_refl _
  | a, k + 1 => Nat.le_trans (ascends_le_add h a k) (h (a + k))

theorem ascends_le {c : Nat → Nat} (h : Ascends c) {a b : Nat} (hab : a ≤ b) :
    c a ≤ c b := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hab
  exact ascends_le_add h a k

theorem climbs_ascends {c : Nat → Nat} (h : Climbs c) : Ascends c :=
  fun n => Nat.le_of_lt (h n)

theorem climbs_add_le {c : Nat → Nat} (h : Climbs c) :
    ∀ n, c 0 + n ≤ c n
  | 0 => Nat.le_refl _
  | n + 1 => Nat.lt_of_le_of_lt (climbs_add_le h n) (h n)

theorem climbs_escape {c : Nat → Nat} (h : Climbs c) (B : Nat) :
    ∃ n, B < c n :=
  ⟨B + 1, Nat.lt_of_lt_of_le (Nat.lt_succ_self B)
    (Nat.le_trans (Nat.le_add_left (B + 1) (c 0)) (climbs_add_le h (B + 1)))⟩

theorem climbs_never_rests {c : Nat → Nat} (h : Climbs c) (n : Nat) :
    ¬ Rests c n :=
  fun hr => Nat.lt_irrefl (c n) (hr ▸ h n)

theorem climbs_seg_le {c : Nat → Nat} :
    ∀ k, (∀ i, i < k → c i < c (i + 1)) → c 0 + k ≤ c k
  | 0, _ => Nat.le_refl _
  | k + 1, h =>
      Nat.lt_of_le_of_lt (climbs_seg_le k (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (h k (Nat.lt_succ_self k))

theorem rests_or_seg_climbs {c : Nat → Nat} (hc : Ascends c) :
    ∀ k, (∃ i, Rests c i) ∨ (∀ i, i < k → c i < c (i + 1))
  | 0 => Or.inr (fun i hi => absurd hi (Nat.not_lt_zero i))
  | k + 1 =>
    match rests_or_seg_climbs hc k with
    | Or.inl h => Or.inl h
    | Or.inr h =>
      match Nat.decEq (c (k + 1)) (c k) with
      | isTrue heq => Or.inl ⟨k, heq⟩
      | isFalse hne =>
        Or.inr (fun i hi =>
          match Nat.lt_or_ge i k with
          | Or.inl hik => h i hik
          | Or.inr hki => by
              have hik : i = k := Nat.le_antisymm (Nat.le_of_lt_succ hi) hki
              subst hik
              exact Nat.lt_of_le_of_ne (hc i) (fun e => hne e.symm))

theorem bounded_rests {c : Nat → Nat} (hc : Ascends c) (B : Nat)
    (hB : ∀ n, c n ≤ B) : ∃ n, Rests c n :=
  match rests_or_seg_climbs hc (B + 1) with
  | Or.inl h => h
  | Or.inr h =>
      absurd
        (Nat.le_trans
          (Nat.le_trans (Nat.le_add_left (B + 1) (c 0)) (climbs_seg_le (B + 1) h))
          (hB (B + 1)))
        (Nat.not_succ_le_self B)

theorem rests_forever_of_seated {c : Nat → Nat} {n : Nat} (h : Seated c n) :
    ∀ m, n ≤ m → Rests c m :=
  fun m hm => (h (m + 1) (Nat.le_succ_of_le hm)).trans (h m hm).symm

theorem seated_of_rests_forever {c : Nat → Nat} {n : Nat}
    (h : ∀ m, n ≤ m → Rests c m) : Seated c n := by
  intro m hm
  induction m with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hm
      subst hn
      rfl
  | succ k ih =>
      match Nat.eq_or_lt_of_le hm with
      | Or.inl heq => rw [heq]
      | Or.inr hlt =>
          have hnk : n ≤ k := Nat.le_of_lt_succ hlt
          exact (h k hnk).trans (ih hnk)

theorem seated_iff_rests_forever {c : Nat → Nat} {n : Nat} :
    Seated c n ↔ ∀ m, n ≤ m → Rests c m :=
  ⟨rests_forever_of_seated, seated_of_rests_forever⟩

theorem seated_never_climbs {c : Nat → Nat} {n : Nat} (h : Seated c n) :
    ¬ Climbs c :=
  fun hcl => climbs_never_rests hcl n (rests_forever_of_seated h n (Nat.le_refl n))

theorem iterStep_add (f : GInt → GInt) :
    ∀ (a b : Nat) (z : GInt), iterStep (a + b) f z = iterStep b f (iterStep a f z)
  | _, 0, _ => rfl
  | a, b + 1, z => congrArg f (iterStep_add f a b z)

theorem closes_laps (f : GInt → GInt) (k : Nat) (h : Closes f k) :
    ∀ m, Closes f (k * m)
  | 0 => fun _ => rfl
  | m + 1 => fun z => by
      show iterStep (k * m + k) f z = z
      rw [iterStep_add f (k * m) k z, closes_laps f k h m z, h z]

theorem lap_carries (f : GInt → GInt) (k : Nat) (h : Closes f k)
    (m r : Nat) (z : GInt) :
    iterStep (k * m + r) f z = iterStep r f z := by
  rw [iterStep_add f (k * m) r z, closes_laps f k h m z]

theorem rot_lap_carries (m r : Nat) (z : GInt) :
    iterStep (4 * m + r) GInt.rot z = iterStep r GInt.rot z :=
  lap_carries GInt.rot 4 spec_closes_four m r z

/-- info: 'Foam.ascends_le' does not depend on any axioms -/
#guard_msgs in #print axioms ascends_le

/-- info: 'Foam.climbs_ascends' does not depend on any axioms -/
#guard_msgs in #print axioms climbs_ascends

/-- info: 'Foam.climbs_escape' does not depend on any axioms -/
#guard_msgs in #print axioms climbs_escape

/-- info: 'Foam.climbs_never_rests' does not depend on any axioms -/
#guard_msgs in #print axioms climbs_never_rests

/-- info: 'Foam.bounded_rests' does not depend on any axioms -/
#guard_msgs in #print axioms bounded_rests

/-- info: 'Foam.seated_iff_rests_forever' does not depend on any axioms -/
#guard_msgs in #print axioms seated_iff_rests_forever

/-- info: 'Foam.seated_never_climbs' does not depend on any axioms -/
#guard_msgs in #print axioms seated_never_climbs

/-- info: 'Foam.iterStep_add' does not depend on any axioms -/
#guard_msgs in #print axioms iterStep_add

/-- info: 'Foam.closes_laps' does not depend on any axioms -/
#guard_msgs in #print axioms closes_laps

/-- info: 'Foam.lap_carries' does not depend on any axioms -/
#guard_msgs in #print axioms lap_carries

/-- info: 'Foam.rot_lap_carries' does not depend on any axioms -/
#guard_msgs in #print axioms rot_lap_carries

end Foam
