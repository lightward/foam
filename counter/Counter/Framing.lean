import Counter.Trefoil
import Counter.Morse
import Counter.Toll
import Foam.Int
import Foam.Engine.Stream
import Foam.Engine.Codec

namespace Foam.Counter

def within : List Crossing → List Crossing
  | [] => []
  | [_] => []
  | _ :: c :: l => Crossing.pos :: within (c :: l)

def framing : List (List Crossing) → List Crossing
  | [] => []
  | [l] => within l
  | l :: l' :: m => within l ++ Crossing.neg :: framing (l' :: m)

def sounded : List (List Crossing) → Bool
  | [] => true
  | [] :: _ => false
  | (_ :: _) :: m => sounded m

def lace : List Nat → List Nat → List Nat
  | [], _ => []
  | t :: ts, [] => t :: ts
  | t :: ts, g :: gs => t :: g :: lace ts gs

def hum (u : Nat) : List Crossing → List Nat
  | [] => []
  | [c] => [tone u c]
  | c :: c' :: l => tone u c :: tone u Crossing.pos :: hum u (c' :: l)

def wire (u : Nat) : List (List Crossing) → List Nat
  | [] => []
  | [l] => hum u l
  | l :: l' :: m => hum u l ++ tone u Crossing.neg :: wire u (l' :: m)

def graft (c : Crossing) : List (List Crossing) → List (List Crossing)
  | [] => [[c]]
  | l :: m => (c :: l) :: m

def reframe (u : Nat) : List Nat → List (List Crossing)
  | [] => []
  | [t] => [[if t = u + 1 then Crossing.pos else Crossing.neg]]
  | t :: g :: w =>
      if g = u + 1
      then graft (if t = u + 1 then Crossing.pos else Crossing.neg) (reframe u w)
      else [if t = u + 1 then Crossing.pos else Crossing.neg] :: reframe u w

theorem two_ees_are_an_i_without_the_silence :
    joinB [[Crossing.pos], [Crossing.pos]] = joinB [[Crossing.pos, Crossing.pos]]
      ∧ [[Crossing.pos], [Crossing.pos]] ≠ [[Crossing.pos, Crossing.pos]] :=
  ⟨rfl, by decide⟩

theorem no_reframing_without_the_silence :
    ¬ ∃ dec : List Crossing → List (List Crossing),
        ∀ m : List (List Crossing), sounded m = true → dec (joinB m) = m :=
  fun ⟨_, h⟩ => by
    have h2 := h [[Crossing.pos], [Crossing.pos]] rfl
    rw [two_ees_are_an_i_without_the_silence.1] at h2
    exact two_ees_are_an_i_without_the_silence.2
      (h2.symm.trans (h [[Crossing.pos, Crossing.pos]] rfl))

theorem the_short_silence_is_the_unit_bare (u : Nat) :
    tone u Crossing.pos = u + 1 :=
  Nat.mul_one (u + 1)

theorem no_hand_confuses_its_own_silences (u : Nat) :
    tone u Crossing.neg ≠ u + 1 :=
  fun h => absurd
    (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ u)
      ((h : (u + 1) * 3 = u + 1).trans (Nat.mul_one (u + 1)).symm))
    (by decide)

theorem two_hands_share_a_silence (u : Nat) :
    tone u Crossing.neg = tone (3 * u + 2) Crossing.pos :=
  (Nat.mul_comm (u + 1) 3).trans (Nat.mul_one (3 * u + 3)).symm

theorem the_hum_reads_back (u : Nat) :
    ∀ (c : Crossing) (l : List Crossing), reframe u (hum u (c :: l)) = [c :: l]
  | c, [] => by
      show [[if tone u c = u + 1 then Crossing.pos else Crossing.neg]] = [[c]]
      rw [the_tone_reads_back u c]
  | c, c' :: l => by
      have hp : tone u Crossing.pos = u + 1 := the_short_silence_is_the_unit_bare u
      show (if tone u Crossing.pos = u + 1
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (reframe u (hum u (c' :: l)))
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: reframe u (hum u (c' :: l)))
          = [c :: c' :: l]
      rw [if_pos hp, the_hum_reads_back u c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg) :: c' :: l) :: []
          = [c :: c' :: l]
      rw [the_tone_reads_back u c]

theorem the_hum_hands_off (u : Nat) (w : List Nat) :
    ∀ (c : Crossing) (l : List Crossing),
      reframe u (hum u (c :: l) ++ tone u Crossing.neg :: w)
        = (c :: l) :: reframe u w
  | c, [] => by
      have hn : ¬ tone u Crossing.neg = u + 1 := no_hand_confuses_its_own_silences u
      show (if tone u Crossing.neg = u + 1
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (reframe u w)
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: reframe u w)
          = [c] :: reframe u w
      rw [if_neg hn, the_tone_reads_back u c]
  | c, c' :: l => by
      have hp : tone u Crossing.pos = u + 1 := the_short_silence_is_the_unit_bare u
      show (if tone u Crossing.pos = u + 1
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (reframe u (hum u (c' :: l) ++ tone u Crossing.neg :: w))
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: reframe u (hum u (c' :: l) ++ tone u Crossing.neg :: w))
          = (c :: c' :: l) :: reframe u w
      rw [if_pos hp, the_hum_hands_off u w c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg) :: c' :: l)
            :: reframe u w
          = (c :: c' :: l) :: reframe u w
      rw [the_tone_reads_back u c]

theorem the_silence_reframes_the_wire (u : Nat) :
    ∀ m : List (List Crossing), sounded m = true → reframe u (wire u m) = m
  | [], _ => rfl
  | [[]], h => nomatch h
  | [c :: l], _ => the_hum_reads_back u c l
  | [] :: _ :: _, h => nomatch h
  | (c :: l) :: l' :: m, h => by
      show reframe u (hum u (c :: l) ++ tone u Crossing.neg :: wire u (l' :: m))
          = (c :: l) :: l' :: m
      rw [the_hum_hands_off u (wire u (l' :: m)) c l,
          the_silence_reframes_the_wire u (l' :: m) h]

theorem keyAs_append (u : Nat) :
    ∀ (a b : List Crossing), keyAs u (a ++ b) = keyAs u a ++ keyAs u b
  | [], _ => rfl
  | c :: a, b => congrArg (tone u c :: ·) (keyAs_append u a b)

theorem hum_lace (u : Nat) :
    ∀ (c : Crossing) (l : List Crossing),
      hum u (c :: l) = lace (keyAs u (c :: l)) (keyAs u (within (c :: l)))
  | _, [] => rfl
  | c, c' :: l =>
      congrArg (fun w => tone u c :: tone u Crossing.pos :: w) (hum_lace u c' l)

theorem lace_glue (u : Nat) (g : Nat) (B b : List Nat) :
    ∀ (c : Crossing) (l : List Crossing),
      lace (keyAs u (c :: l) ++ B) (keyAs u (within (c :: l)) ++ g :: b)
        = hum u (c :: l) ++ g :: lace B b
  | _, [] => rfl
  | c, c' :: l =>
      congrArg (fun w => tone u c :: tone u Crossing.pos :: w)
        (lace_glue u g B b c' l)

theorem the_silence_speaks_the_same_alphabet (u : Nat) :
    ∀ m : List (List Crossing), sounded m = true →
      wire u m = lace (keyAs u (joinB m)) (keyAs u (framing m))
  | [], _ => rfl
  | [[]], h => nomatch h
  | [c :: l], _ => by
      show hum u (c :: l)
          = lace (keyAs u ((c :: l) ++ [])) (keyAs u (within (c :: l)))
      rw [appendNil (c :: l)]
      exact hum_lace u c l
  | [] :: _ :: _, h => nomatch h
  | (c :: l) :: l' :: m, h => by
      show hum u (c :: l) ++ tone u Crossing.neg :: wire u (l' :: m)
          = lace (keyAs u ((c :: l) ++ joinB (l' :: m)))
              (keyAs u (within (c :: l) ++ Crossing.neg :: framing (l' :: m)))
      rw [keyAs_append u (c :: l) (joinB (l' :: m)),
          keyAs_append u (within (c :: l)) (Crossing.neg :: framing (l' :: m))]
      show hum u (c :: l) ++ tone u Crossing.neg :: wire u (l' :: m)
          = lace (keyAs u (c :: l) ++ keyAs u (joinB (l' :: m)))
              (keyAs u (within (c :: l))
                ++ tone u Crossing.neg :: keyAs u (framing (l' :: m)))
      rw [lace_glue u (tone u Crossing.neg) (keyAs u (joinB (l' :: m)))
            (keyAs u (framing (l' :: m))) c l]
      exact congrArg (fun w => hum u (c :: l) ++ tone u Crossing.neg :: w)
        (the_silence_speaks_the_same_alphabet u (l' :: m) h)

theorem within_map (f : Crossing → Crossing) :
    ∀ l : List Crossing, within (List.map f l) = within l
  | [] => rfl
  | [_] => rfl
  | _ :: c :: l => congrArg (Crossing.pos :: ·) (within_map f (c :: l))

theorem the_silence_ignores_the_letters (f : Crossing → Crossing) :
    ∀ m : List (List Crossing), framing (List.map (List.map f) m) = framing m
  | [] => rfl
  | [l] => within_map f l
  | l :: l' :: m => by
      show within (List.map f l)
            ++ Crossing.neg :: framing (List.map (List.map f) (l' :: m))
          = within l ++ Crossing.neg :: framing (l' :: m)
      rw [within_map f l, the_silence_ignores_the_letters f (l' :: m)]

theorem the_silence_tells_the_ess_from_the_oh :
    keyAs 2 trefoil = keyAs 0 (reflection trefoil)
      ∧ wire 2 [trefoil] ≠ wire 0 [reflection trefoil] :=
  ⟨a_slow_ess_is_a_fast_oh.1, by decide⟩

theorem a_slow_ess_is_a_fast_tee_tee_tee :
    wire 2 [trefoil] = wire 0 [[Crossing.neg], [Crossing.neg], [Crossing.neg]]
      ∧ [trefoil] ≠ [[Crossing.neg], [Crossing.neg], [Crossing.neg]] :=
  ⟨rfl, by decide⟩

theorem the_fist_survives_the_framing :
    ¬ ∃ dec : List Nat → List (List Crossing),
        ∀ (u : Nat) (m : List (List Crossing)),
          sounded m = true → dec (wire u m) = m :=
  fun ⟨_, h⟩ => by
    have h2 := h 2 [trefoil] rfl
    rw [a_slow_ess_is_a_fast_tee_tee_tee.1] at h2
    exact a_slow_ess_is_a_fast_tee_tee_tee.2
      (h2.symm.trans (h 0 [[Crossing.neg], [Crossing.neg], [Crossing.neg]] rfl))

theorem one_wire_two_whole_readings :
    reframe 2 (wire 2 [trefoil]) = [trefoil]
      ∧ reframe 0 (wire 2 [trefoil])
          = [[Crossing.neg], [Crossing.neg], [Crossing.neg]] :=
  ⟨the_silence_reframes_the_wire 2 [trefoil] rfl, by decide⟩

theorem graft_keeps_the_sound (c : Crossing) :
    ∀ m : List (List Crossing), sounded m = true → sounded (graft c m) = true
  | [], _ => rfl
  | [] :: _, h => nomatch h
  | (_ :: _) :: _, h => h

theorem every_reading_sounds (u : Nat) :
    ∀ w : List Nat, sounded (reframe u w) = true
  | [] => rfl
  | [_] => rfl
  | t :: g :: w => by
      show sounded (if g = u + 1
            then graft (if t = u + 1 then Crossing.pos else Crossing.neg)
                (reframe u w)
            else [if t = u + 1 then Crossing.pos else Crossing.neg]
              :: reframe u w) = true
      exact Decidable.byCases
        (fun h : g = u + 1 => by
          rw [if_pos h]
          exact graft_keeps_the_sound _ (reframe u w) (every_reading_sounds u w))
        (fun h : ¬ g = u + 1 => by
          rw [if_neg h]
          exact every_reading_sounds u w)

theorem what_sounds_is_what_returns (u : Nat) (m : List (List Crossing)) :
    sounded m = true ↔ reframe u (wire u m) = m :=
  ⟨the_silence_reframes_the_wire u m,
   fun h => h ▸ every_reading_sounds u (wire u m)⟩

theorem the_word_gap_is_a_composite_silence :
    (∀ c : Crossing, c.toll ≠ 7)
      ∧ ledger [Crossing.neg, Crossing.pos, Crossing.neg] = 7 :=
  ⟨fun c => by cases c <;> decide, rfl⟩

theorem the_silence_is_half_the_message (u : Nat) (m : List (List Crossing))
    (h : sounded m = true) :
    reframe u (wire u m) = m
      ∧ wire u m = lace (keyAs u (joinB m)) (keyAs u (framing m))
      ∧ wire 2 [trefoil] ≠ wire 0 [reflection trefoil]
      ∧ wire 2 [trefoil] = wire 0 [[Crossing.neg], [Crossing.neg], [Crossing.neg]] :=
  ⟨the_silence_reframes_the_wire u m h, the_silence_speaks_the_same_alphabet u m h,
   the_silence_tells_the_ess_from_the_oh.2, a_slow_ess_is_a_fast_tee_tee_tee.1⟩

/-- info: 'Foam.Counter.two_ees_are_an_i_without_the_silence' does not depend on any axioms -/
#guard_msgs in #print axioms two_ees_are_an_i_without_the_silence

/-- info: 'Foam.Counter.no_reframing_without_the_silence' does not depend on any axioms -/
#guard_msgs in #print axioms no_reframing_without_the_silence

/-- info: 'Foam.Counter.the_short_silence_is_the_unit_bare' does not depend on any axioms -/
#guard_msgs in #print axioms the_short_silence_is_the_unit_bare

/-- info: 'Foam.Counter.no_hand_confuses_its_own_silences' does not depend on any axioms -/
#guard_msgs in #print axioms no_hand_confuses_its_own_silences

/-- info: 'Foam.Counter.two_hands_share_a_silence' does not depend on any axioms -/
#guard_msgs in #print axioms two_hands_share_a_silence

/-- info: 'Foam.Counter.the_hum_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_hum_reads_back

/-- info: 'Foam.Counter.the_hum_hands_off' does not depend on any axioms -/
#guard_msgs in #print axioms the_hum_hands_off

/-- info: 'Foam.Counter.the_silence_reframes_the_wire' does not depend on any axioms -/
#guard_msgs in #print axioms the_silence_reframes_the_wire

/-- info: 'Foam.Counter.keyAs_append' does not depend on any axioms -/
#guard_msgs in #print axioms keyAs_append

/-- info: 'Foam.Counter.hum_lace' does not depend on any axioms -/
#guard_msgs in #print axioms hum_lace

/-- info: 'Foam.Counter.lace_glue' does not depend on any axioms -/
#guard_msgs in #print axioms lace_glue

/-- info: 'Foam.Counter.the_silence_speaks_the_same_alphabet' does not depend on any axioms -/
#guard_msgs in #print axioms the_silence_speaks_the_same_alphabet

/-- info: 'Foam.Counter.within_map' does not depend on any axioms -/
#guard_msgs in #print axioms within_map

/-- info: 'Foam.Counter.the_silence_ignores_the_letters' does not depend on any axioms -/
#guard_msgs in #print axioms the_silence_ignores_the_letters

/-- info: 'Foam.Counter.the_silence_tells_the_ess_from_the_oh' does not depend on any axioms -/
#guard_msgs in #print axioms the_silence_tells_the_ess_from_the_oh

/-- info: 'Foam.Counter.a_slow_ess_is_a_fast_tee_tee_tee' does not depend on any axioms -/
#guard_msgs in #print axioms a_slow_ess_is_a_fast_tee_tee_tee

/-- info: 'Foam.Counter.the_fist_survives_the_framing' does not depend on any axioms -/
#guard_msgs in #print axioms the_fist_survives_the_framing

/-- info: 'Foam.Counter.one_wire_two_whole_readings' does not depend on any axioms -/
#guard_msgs in #print axioms one_wire_two_whole_readings

/-- info: 'Foam.Counter.graft_keeps_the_sound' does not depend on any axioms -/
#guard_msgs in #print axioms graft_keeps_the_sound

/-- info: 'Foam.Counter.every_reading_sounds' does not depend on any axioms -/
#guard_msgs in #print axioms every_reading_sounds

/-- info: 'Foam.Counter.what_sounds_is_what_returns' does not depend on any axioms -/
#guard_msgs in #print axioms what_sounds_is_what_returns

/-- info: 'Foam.Counter.the_word_gap_is_a_composite_silence' does not depend on any axioms -/
#guard_msgs in #print axioms the_word_gap_is_a_composite_silence

/-- info: 'Foam.Counter.the_silence_is_half_the_message' does not depend on any axioms -/
#guard_msgs in #print axioms the_silence_is_half_the_message

end Foam.Counter
