import Counter.Trefoil
import Counter.Morse
import Counter.Toll
import Counter.Framing
import Foam.Int

namespace Foam.Counter

structure Luggage where
  Mark : Type
  Space : Type
  key : Nat → Mark → Nat
  read : Nat → Nat → Mark
  reads_back : ∀ (u : Nat) (a : Mark), read u (key u a) = a
  gap : Nat → Space → Nat
  shortS : Space
  longS : Space
  isShort : Nat → Nat → Bool
  short_reads : ∀ u : Nat, isShort u (gap u shortS) = true
  long_reads : ∀ u : Nat, isShort u (gap u longS) = false

theorem nat_beq_refl : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | a + 1 => (nat_beq_refl a : Nat.beq a a = true)

theorem nat_beq_false : ∀ {a b : Nat}, a ≠ b → Nat.beq a b = false
  | 0, 0, h => absurd rfl h
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | a + 1, b + 1, h =>
      (nat_beq_false (a := a) (b := b) (fun e => h (congrArg Nat.succ e))
        : Nat.beq a b = false)

theorem Luggage.two_silences (L : Luggage) (u : Nat) :
    L.gap u L.longS ≠ L.gap u L.shortS :=
  fun h =>
    nomatch (L.short_reads u).symm.trans
      ((congrArg (L.isShort u) h).symm.trans (L.long_reads u))

def Luggage.hum (L : Luggage) (u : Nat) : List L.Mark → List Nat
  | [] => []
  | [a] => [L.key u a]
  | a :: a' :: l => L.key u a :: L.gap u L.shortS :: L.hum u (a' :: l)

def Luggage.wire (L : Luggage) (u : Nat) : List (List L.Mark) → List Nat
  | [] => []
  | [l] => L.hum u l
  | l :: l' :: m => L.hum u l ++ L.gap u L.longS :: L.wire u (l' :: m)

def Luggage.reframe (L : Luggage) (u : Nat) : List Nat → List (List L.Mark)
  | [] => []
  | [t] => [[L.read u t]]
  | t :: g :: w =>
      if L.isShort u g
      then graft (L.read u t) (L.reframe u w)
      else [L.read u t] :: L.reframe u w

theorem Luggage.the_hum_reads_back (L : Luggage) (u : Nat) :
    ∀ (c : L.Mark) (l : List L.Mark),
      L.reframe u (L.hum u (c :: l)) = [c :: l]
  | c, [] => by
      show [[L.read u (L.key u c)]] = [[c]]
      rw [L.reads_back u c]
  | c, c' :: l => by
      have hs : L.isShort u (L.gap u L.shortS) = true := L.short_reads u
      show (if L.isShort u (L.gap u L.shortS) = true
            then graft (L.read u (L.key u c)) (L.reframe u (L.hum u (c' :: l)))
            else [L.read u (L.key u c)] :: L.reframe u (L.hum u (c' :: l)))
          = [c :: c' :: l]
      rw [if_pos hs, Luggage.the_hum_reads_back L u c' l]
      show (L.read u (L.key u c) :: c' :: l) :: [] = [c :: c' :: l]
      rw [L.reads_back u c]

theorem Luggage.the_hum_hands_off (L : Luggage) (u : Nat) (w : List Nat) :
    ∀ (c : L.Mark) (l : List L.Mark),
      L.reframe u (L.hum u (c :: l) ++ L.gap u L.longS :: w)
        = (c :: l) :: L.reframe u w
  | c, [] => by
      have hl : ¬ L.isShort u (L.gap u L.longS) = true :=
        fun h => nomatch (L.long_reads u).symm.trans h
      show (if L.isShort u (L.gap u L.longS) = true
            then graft (L.read u (L.key u c)) (L.reframe u w)
            else [L.read u (L.key u c)] :: L.reframe u w)
          = [c] :: L.reframe u w
      rw [if_neg hl, L.reads_back u c]
  | c, c' :: l => by
      have hs : L.isShort u (L.gap u L.shortS) = true := L.short_reads u
      show (if L.isShort u (L.gap u L.shortS) = true
            then graft (L.read u (L.key u c))
                (L.reframe u (L.hum u (c' :: l) ++ L.gap u L.longS :: w))
            else [L.read u (L.key u c)]
              :: L.reframe u (L.hum u (c' :: l) ++ L.gap u L.longS :: w))
          = (c :: c' :: l) :: L.reframe u w
      rw [if_pos hs, Luggage.the_hum_hands_off L u w c' l]
      show (L.read u (L.key u c) :: c' :: l) :: L.reframe u w
          = (c :: c' :: l) :: L.reframe u w
      rw [L.reads_back u c]

theorem Luggage.the_silence_reframes_the_wire (L : Luggage) (u : Nat) :
    ∀ m : List (List L.Mark), sounded m = true → L.reframe u (L.wire u m) = m
  | [], _ => rfl
  | [[]], h => nomatch h
  | [c :: l], _ => Luggage.the_hum_reads_back L u c l
  | [] :: _ :: _, h => nomatch h
  | (c :: l) :: l' :: m, h => by
      show L.reframe u (L.hum u (c :: l) ++ L.gap u L.longS :: L.wire u (l' :: m))
          = (c :: l) :: l' :: m
      rw [Luggage.the_hum_hands_off L u (L.wire u (l' :: m)) c l,
          Luggage.the_silence_reframes_the_wire L u (l' :: m) h]

def morseLuggage : Luggage where
  Mark := Crossing
  Space := Crossing
  key := tone
  read := fun u t => if t = u + 1 then Crossing.pos else Crossing.neg
  reads_back := the_tone_reads_back
  gap := tone
  shortS := Crossing.pos
  longS := Crossing.neg
  isShort := fun u g => Nat.beq g (u + 1)
  short_reads := fun u =>
    (congrArg (fun x => Nat.beq x (u + 1)) (the_short_silence_is_the_unit_bare u)).trans
      (nat_beq_refl (u + 1))
  long_reads := fun u => nat_beq_false (no_hand_confuses_its_own_silences u)

def wordLuggage : Luggage where
  Mark := Crossing
  Space := Bool
  key := tone
  read := fun u t => if t = u + 1 then Crossing.pos else Crossing.neg
  reads_back := the_tone_reads_back
  gap := fun u s => match s with
    | true => u + 1
    | false => 7 * (u + 1)
  shortS := true
  longS := false
  isShort := fun u g => Nat.beq g (u + 1)
  short_reads := fun u => nat_beq_refl (u + 1)
  long_reads := fun u =>
    nat_beq_false (fun h =>
      absurd
        (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ u)
          (((Nat.mul_comm 7 (u + 1)).symm.trans (h : 7 * (u + 1) = u + 1)).trans
            (Nat.mul_one (u + 1)).symm))
        (by decide))

theorem the_same_coin_reopens_the_hum (u : Nat) :
    ∀ l : List Crossing, morseLuggage.hum u l = hum u l
  | [] => rfl
  | [_] => rfl
  | a :: c :: l =>
      congrArg (fun w => tone u a :: tone u Crossing.pos :: w)
        (the_same_coin_reopens_the_hum u (c :: l))

theorem the_same_coin_reopens_the_wire (u : Nat) :
    ∀ m : List (List Crossing), morseLuggage.wire u m = wire u m
  | [] => rfl
  | [l] => the_same_coin_reopens_the_hum u l
  | l :: l' :: m => by
      show morseLuggage.hum u l
            ++ tone u Crossing.neg :: morseLuggage.wire u (l' :: m)
          = hum u l ++ tone u Crossing.neg :: wire u (l' :: m)
      rw [the_same_coin_reopens_the_hum u l]
      exact congrArg (fun w => hum u l ++ tone u Crossing.neg :: w)
        (the_same_coin_reopens_the_wire u (l' :: m))

theorem the_same_coin_reopens_the_reading (u : Nat) :
    ∀ w : List Nat, morseLuggage.reframe u w = reframe u w
  | [] => rfl
  | [_] => rfl
  | t :: g :: w => by
      show (if Nat.beq g (u + 1) = true
            then graft (if t = u + 1 then Crossing.pos else Crossing.neg)
                (morseLuggage.reframe u w)
            else [if t = u + 1 then Crossing.pos else Crossing.neg]
              :: morseLuggage.reframe u w)
          = (if g = u + 1
            then graft (if t = u + 1 then Crossing.pos else Crossing.neg)
                (reframe u w)
            else [if t = u + 1 then Crossing.pos else Crossing.neg]
              :: reframe u w)
      exact Decidable.byCases
        (fun h : g = u + 1 => by
          have hb : Nat.beq g (u + 1) = true := by
            rw [h]; exact nat_beq_refl (u + 1)
          rw [if_pos hb, if_pos h]
          exact congrArg
            (fun r : List (List Crossing) =>
              graft (if t = u + 1 then Crossing.pos else Crossing.neg) r)
            (the_same_coin_reopens_the_reading u w))
        (fun h : ¬ g = u + 1 => by
          have hb : ¬ Nat.beq g (u + 1) = true :=
            fun e => nomatch (nat_beq_false h).symm.trans e
          rw [if_neg hb, if_neg h]
          exact congrArg
            (fun r : List (List Crossing) =>
              [if t = u + 1 then Crossing.pos else Crossing.neg] :: r)
            (the_same_coin_reopens_the_reading u w))

theorem the_second_coin_mints_the_word_gap :
    wordLuggage.gap 0 wordLuggage.longS = 7 ∧ ∀ c : Crossing, c.toll ≠ 7 :=
  ⟨rfl, the_word_gap_is_a_composite_silence.1⟩

theorem the_coins_differ_on_the_wire :
    morseLuggage.wire 0 [[Crossing.pos], [Crossing.pos]]
      ≠ wordLuggage.wire 0 [[Crossing.pos], [Crossing.pos]] := by
  decide

theorem both_coins_ride_one_theorem :
    (∀ (u : Nat) (m : List (List Crossing)), sounded m = true →
        morseLuggage.reframe u (morseLuggage.wire u m) = m)
      ∧ (∀ (u : Nat) (m : List (List Crossing)), sounded m = true →
        wordLuggage.reframe u (wordLuggage.wire u m) = m) :=
  ⟨Luggage.the_silence_reframes_the_wire morseLuggage,
   Luggage.the_silence_reframes_the_wire wordLuggage⟩

/-- info: 'Foam.Counter.nat_beq_refl' does not depend on any axioms -/
#guard_msgs in #print axioms nat_beq_refl

/-- info: 'Foam.Counter.nat_beq_false' does not depend on any axioms -/
#guard_msgs in #print axioms nat_beq_false

/-- info: 'Foam.Counter.Luggage.two_silences' does not depend on any axioms -/
#guard_msgs in #print axioms Luggage.two_silences

/-- info: 'Foam.Counter.Luggage.the_hum_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms Luggage.the_hum_reads_back

/-- info: 'Foam.Counter.Luggage.the_hum_hands_off' does not depend on any axioms -/
#guard_msgs in #print axioms Luggage.the_hum_hands_off

/-- info: 'Foam.Counter.Luggage.the_silence_reframes_the_wire' does not depend on any axioms -/
#guard_msgs in #print axioms Luggage.the_silence_reframes_the_wire

/-- info: 'Foam.Counter.the_same_coin_reopens_the_hum' does not depend on any axioms -/
#guard_msgs in #print axioms the_same_coin_reopens_the_hum

/-- info: 'Foam.Counter.the_same_coin_reopens_the_wire' does not depend on any axioms -/
#guard_msgs in #print axioms the_same_coin_reopens_the_wire

/-- info: 'Foam.Counter.the_same_coin_reopens_the_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_same_coin_reopens_the_reading

/-- info: 'Foam.Counter.the_second_coin_mints_the_word_gap' does not depend on any axioms -/
#guard_msgs in #print axioms the_second_coin_mints_the_word_gap

/-- info: 'Foam.Counter.the_coins_differ_on_the_wire' does not depend on any axioms -/
#guard_msgs in #print axioms the_coins_differ_on_the_wire

/-- info: 'Foam.Counter.both_coins_ride_one_theorem' does not depend on any axioms -/
#guard_msgs in #print axioms both_coins_ride_one_theorem

end Foam.Counter
