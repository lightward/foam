import Counter.Trefoil
import Counter.Morse
import Counter.Framing
import Counter.Luggage
import Foam.Int

namespace Foam.Counter

theorem gaps_split (u i j : Nat) (h : i ≠ j) : (u + 1) * i ≠ (u + 1) * j :=
  fun he => h (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ u) he)

def hum2 (u : Nat) : Crossing → List (Bool × Crossing) → List Nat
  | c, [] => [tone u c]
  | c, (b, c') :: l =>
      tone u c :: (if b then tone u Crossing.pos else (u + 1) * 2) :: hum2 u c' l

def wire2 (u : Nat) : List (Crossing × List (Bool × Crossing)) → List Nat
  | [] => []
  | [(c, l)] => hum2 u c l
  | (c, l) :: p :: m => hum2 u c l ++ tone u Crossing.neg :: wire2 u (p :: m)

def graft2 (c : Crossing) (b : Bool) :
    List (Crossing × List (Bool × Crossing))
      → List (Crossing × List (Bool × Crossing))
  | [] => [(c, [])]
  | (c', l) :: m => (c, (b, c') :: l) :: m

def reframe2 (u : Nat) : List Nat → List (Crossing × List (Bool × Crossing))
  | [] => []
  | [t] => [(if t = u + 1 then Crossing.pos else Crossing.neg, [])]
  | t :: g :: w =>
      if g = tone u Crossing.neg
      then (if t = u + 1 then Crossing.pos else Crossing.neg, []) :: reframe2 u w
      else graft2 (if t = u + 1 then Crossing.pos else Crossing.neg)
          (if g = u + 1 then true else false) (reframe2 u w)

def relief : List (Crossing × List (Bool × Crossing)) → List (List Crossing)
  | [] => []
  | (c, l) :: m => (c :: l.map Prod.snd) :: relief m

def undertow : List (Crossing × List (Bool × Crossing)) → List (List Bool)
  | [] => []
  | (_, l) :: m => l.map Prod.fst :: undertow m

theorem the_braided_hum_reads_back (u : Nat) :
    ∀ (c : Crossing) (l : List (Bool × Crossing)),
      reframe2 u (hum2 u c l) = [(c, l)]
  | c, [] => by
      show [(if tone u c = u + 1 then Crossing.pos else Crossing.neg, [])]
          = [(c, [])]
      rw [the_tone_reads_back u c]
  | c, (true, c') :: l => by
      have hng : ¬ tone u Crossing.pos = tone u Crossing.neg :=
        gaps_split u 1 3 (by decide)
      show (if tone u Crossing.pos = tone u Crossing.neg
            then (if tone u c = u + 1 then Crossing.pos else Crossing.neg, [])
                :: reframe2 u (hum2 u c' l)
            else graft2 (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (if tone u Crossing.pos = u + 1 then true else false)
                (reframe2 u (hum2 u c' l)))
          = [(c, (true, c') :: l)]
      rw [if_neg hng, if_pos (the_short_silence_is_the_unit_bare u),
          the_braided_hum_reads_back u c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg),
            (true, c') :: l) :: [] = [(c, (true, c') :: l)]
      rw [the_tone_reads_back u c]
  | c, (false, c') :: l => by
      have hng : ¬ (u + 1) * 2 = tone u Crossing.neg :=
        gaps_split u 2 3 (by decide)
      have hnb : ¬ (u + 1) * 2 = u + 1 :=
        fun h => gaps_split u 2 1 (by decide)
          (h.trans (Nat.mul_one (u + 1)).symm)
      show (if (u + 1) * 2 = tone u Crossing.neg
            then (if tone u c = u + 1 then Crossing.pos else Crossing.neg, [])
                :: reframe2 u (hum2 u c' l)
            else graft2 (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (if (u + 1) * 2 = u + 1 then true else false)
                (reframe2 u (hum2 u c' l)))
          = [(c, (false, c') :: l)]
      rw [if_neg hng, if_neg hnb, the_braided_hum_reads_back u c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg),
            (false, c') :: l) :: [] = [(c, (false, c') :: l)]
      rw [the_tone_reads_back u c]

theorem the_braided_hum_hands_off (u : Nat) (w : List Nat) :
    ∀ (c : Crossing) (l : List (Bool × Crossing)),
      reframe2 u (hum2 u c l ++ tone u Crossing.neg :: w)
        = (c, l) :: reframe2 u w
  | c, [] => by
      show (if tone u Crossing.neg = tone u Crossing.neg
            then (if tone u c = u + 1 then Crossing.pos else Crossing.neg, [])
                :: reframe2 u w
            else graft2 (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (if tone u Crossing.neg = u + 1 then true else false)
                (reframe2 u w))
          = (c, []) :: reframe2 u w
      rw [if_pos rfl, the_tone_reads_back u c]
  | c, (true, c') :: l => by
      have hng : ¬ tone u Crossing.pos = tone u Crossing.neg :=
        gaps_split u 1 3 (by decide)
      show (if tone u Crossing.pos = tone u Crossing.neg
            then (if tone u c = u + 1 then Crossing.pos else Crossing.neg, [])
                :: reframe2 u (hum2 u c' l ++ tone u Crossing.neg :: w)
            else graft2 (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (if tone u Crossing.pos = u + 1 then true else false)
                (reframe2 u (hum2 u c' l ++ tone u Crossing.neg :: w)))
          = (c, (true, c') :: l) :: reframe2 u w
      rw [if_neg hng, if_pos (the_short_silence_is_the_unit_bare u),
          the_braided_hum_hands_off u w c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg),
            (true, c') :: l) :: reframe2 u w
          = (c, (true, c') :: l) :: reframe2 u w
      rw [the_tone_reads_back u c]
  | c, (false, c') :: l => by
      have hng : ¬ (u + 1) * 2 = tone u Crossing.neg :=
        gaps_split u 2 3 (by decide)
      have hnb : ¬ (u + 1) * 2 = u + 1 :=
        fun h => gaps_split u 2 1 (by decide)
          (h.trans (Nat.mul_one (u + 1)).symm)
      show (if (u + 1) * 2 = tone u Crossing.neg
            then (if tone u c = u + 1 then Crossing.pos else Crossing.neg, [])
                :: reframe2 u (hum2 u c' l ++ tone u Crossing.neg :: w)
            else graft2 (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (if (u + 1) * 2 = u + 1 then true else false)
                (reframe2 u (hum2 u c' l ++ tone u Crossing.neg :: w)))
          = (c, (false, c') :: l) :: reframe2 u w
      rw [if_neg hng, if_neg hnb, the_braided_hum_hands_off u w c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg),
            (false, c') :: l) :: reframe2 u w
          = (c, (false, c') :: l) :: reframe2 u w
      rw [the_tone_reads_back u c]

theorem the_braid_reframes_whole (u : Nat) :
    ∀ m : List (Crossing × List (Bool × Crossing)),
      reframe2 u (wire2 u m) = m
  | [] => rfl
  | [(c, l)] => the_braided_hum_reads_back u c l
  | (c, l) :: p :: m => by
      show reframe2 u (hum2 u c l ++ tone u Crossing.neg :: wire2 u (p :: m))
          = (c, l) :: p :: m
      rw [the_braided_hum_hands_off u (wire2 u (p :: m)) c l,
          the_braid_reframes_whole u (p :: m)]

theorem the_relief_survives_the_undertow (u : Nat)
    (m : List (Crossing × List (Bool × Crossing))) :
    relief (reframe2 u (wire2 u m)) = relief m :=
  congrArg relief (the_braid_reframes_whole u m)

theorem the_undertow_arrives_whole (u : Nat)
    (m : List (Crossing × List (Bool × Crossing))) :
    undertow (reframe2 u (wire2 u m)) = undertow m :=
  congrArg undertow (the_braid_reframes_whole u m)

theorem two_undertows_one_relief (u : Nat)
    {m m' : List (Crossing × List (Bool × Crossing))}
    (h : relief m = relief m') :
    relief (reframe2 u (wire2 u m)) = relief (reframe2 u (wire2 u m')) :=
  (the_relief_survives_the_undertow u m).trans
    (h.trans (the_relief_survives_the_undertow u m').symm)

theorem the_point_reader_splits_the_braid :
    reframe 0 (wire2 0 [(Crossing.pos, [(false, Crossing.pos)])])
        = [[Crossing.pos], [Crossing.pos]]
      ∧ relief (reframe2 0 (wire2 0 [(Crossing.pos, [(false, Crossing.pos)])]))
        = [[Crossing.pos, Crossing.pos]] :=
  ⟨rfl, rfl⟩

def braidCoarse : Luggage where
  Mark := Crossing
  Space := Crossing
  key := tone
  read := fun u t => if t = u + 1 then Crossing.pos else Crossing.neg
  reads_back := the_tone_reads_back
  gap := tone
  shortS := Crossing.pos
  longS := Crossing.neg
  isShort := fun u g => Bool.not (Nat.beq g (tone u Crossing.neg))
  short_reads := fun u =>
    congrArg Bool.not (nat_beq_false (gaps_split u 1 3 (by decide)))
  long_reads := fun u =>
    congrArg Bool.not (nat_beq_refl (tone u Crossing.neg))

theorem the_coarse_hum_reads_the_surface (u : Nat) :
    ∀ (c : Crossing) (l : List (Bool × Crossing)),
      braidCoarse.reframe u (hum2 u c l) = [c :: l.map Prod.snd]
  | c, [] => by
      show [[if tone u c = u + 1 then Crossing.pos else Crossing.neg]] = [[c]]
      rw [the_tone_reads_back u c]
  | c, (true, c') :: l => by
      have hs : braidCoarse.isShort u (tone u Crossing.pos) = true :=
        braidCoarse.short_reads u
      show (if braidCoarse.isShort u (tone u Crossing.pos) = true
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (braidCoarse.reframe u (hum2 u c' l))
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: braidCoarse.reframe u (hum2 u c' l))
          = [c :: c' :: l.map Prod.snd]
      rw [if_pos hs, the_coarse_hum_reads_the_surface u c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg)
            :: c' :: l.map Prod.snd) :: []
          = [c :: c' :: l.map Prod.snd]
      rw [the_tone_reads_back u c]
  | c, (false, c') :: l => by
      have hs : braidCoarse.isShort u ((u + 1) * 2) = true :=
        congrArg Bool.not (nat_beq_false (gaps_split u 2 3 (by decide)))
      show (if braidCoarse.isShort u ((u + 1) * 2) = true
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (braidCoarse.reframe u (hum2 u c' l))
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: braidCoarse.reframe u (hum2 u c' l))
          = [c :: c' :: l.map Prod.snd]
      rw [if_pos hs, the_coarse_hum_reads_the_surface u c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg)
            :: c' :: l.map Prod.snd) :: []
          = [c :: c' :: l.map Prod.snd]
      rw [the_tone_reads_back u c]

theorem the_coarse_hum_hands_off (u : Nat) (w : List Nat) :
    ∀ (c : Crossing) (l : List (Bool × Crossing)),
      braidCoarse.reframe u (hum2 u c l ++ tone u Crossing.neg :: w)
        = (c :: l.map Prod.snd) :: braidCoarse.reframe u w
  | c, [] => by
      have hl : ¬ braidCoarse.isShort u (tone u Crossing.neg) = true :=
        fun h => nomatch (braidCoarse.long_reads u).symm.trans h
      show (if braidCoarse.isShort u (tone u Crossing.neg) = true
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (braidCoarse.reframe u w)
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: braidCoarse.reframe u w)
          = [c] :: braidCoarse.reframe u w
      rw [if_neg hl, the_tone_reads_back u c]
  | c, (true, c') :: l => by
      have hs : braidCoarse.isShort u (tone u Crossing.pos) = true :=
        braidCoarse.short_reads u
      show (if braidCoarse.isShort u (tone u Crossing.pos) = true
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (braidCoarse.reframe u
                  (hum2 u c' l ++ tone u Crossing.neg :: w))
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: braidCoarse.reframe u
                  (hum2 u c' l ++ tone u Crossing.neg :: w))
          = (c :: c' :: l.map Prod.snd) :: braidCoarse.reframe u w
      rw [if_pos hs, the_coarse_hum_hands_off u w c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg)
            :: c' :: l.map Prod.snd) :: braidCoarse.reframe u w
          = (c :: c' :: l.map Prod.snd) :: braidCoarse.reframe u w
      rw [the_tone_reads_back u c]
  | c, (false, c') :: l => by
      have hs : braidCoarse.isShort u ((u + 1) * 2) = true :=
        congrArg Bool.not (nat_beq_false (gaps_split u 2 3 (by decide)))
      show (if braidCoarse.isShort u ((u + 1) * 2) = true
            then graft (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
                (braidCoarse.reframe u
                  (hum2 u c' l ++ tone u Crossing.neg :: w))
            else [if tone u c = u + 1 then Crossing.pos else Crossing.neg]
              :: braidCoarse.reframe u
                  (hum2 u c' l ++ tone u Crossing.neg :: w))
          = (c :: c' :: l.map Prod.snd) :: braidCoarse.reframe u w
      rw [if_pos hs, the_coarse_hum_hands_off u w c' l]
      show ((if tone u c = u + 1 then Crossing.pos else Crossing.neg)
            :: c' :: l.map Prod.snd) :: braidCoarse.reframe u w
          = (c :: c' :: l.map Prod.snd) :: braidCoarse.reframe u w
      rw [the_tone_reads_back u c]

theorem the_coarse_luggage_reads_the_relief (u : Nat) :
    ∀ m : List (Crossing × List (Bool × Crossing)),
      braidCoarse.reframe u (wire2 u m) = relief m
  | [] => rfl
  | [(c, l)] => the_coarse_hum_reads_the_surface u c l
  | (c, l) :: p :: m => by
      show braidCoarse.reframe u
            (hum2 u c l ++ tone u Crossing.neg :: wire2 u (p :: m))
          = (c :: l.map Prod.snd) :: relief (p :: m)
      rw [the_coarse_hum_hands_off u (wire2 u (p :: m)) c l]
      exact congrArg ((c :: l.map Prod.snd) :: ·)
        (the_coarse_luggage_reads_the_relief u (p :: m))

theorem the_weather_eye_is_generic (u : Nat)
    {m m' : List (Crossing × List (Bool × Crossing))}
    (h : relief m = relief m') :
    braidCoarse.reframe u (wire2 u m) = braidCoarse.reframe u (wire2 u m') :=
  (the_coarse_luggage_reads_the_relief u m).trans
    (h.trans (the_coarse_luggage_reads_the_relief u m').symm)

theorem the_coarse_coin_reopens_the_hum (u : Nat) :
    ∀ l : List Crossing, braidCoarse.hum u l = hum u l
  | [] => rfl
  | [_] => rfl
  | a :: c :: l =>
      congrArg (fun w => tone u a :: tone u Crossing.pos :: w)
        (the_coarse_coin_reopens_the_hum u (c :: l))

theorem the_coarse_coin_reopens_the_wire (u : Nat) :
    ∀ m : List (List Crossing), braidCoarse.wire u m = wire u m
  | [] => rfl
  | [l] => the_coarse_coin_reopens_the_hum u l
  | l :: l' :: m => by
      show braidCoarse.hum u l
            ++ tone u Crossing.neg :: braidCoarse.wire u (l' :: m)
          = hum u l ++ tone u Crossing.neg :: wire u (l' :: m)
      rw [the_coarse_coin_reopens_the_hum u l]
      exact congrArg (fun w => hum u l ++ tone u Crossing.neg :: w)
        (the_coarse_coin_reopens_the_wire u (l' :: m))

theorem the_silence_carries_a_second_message (u : Nat)
    (m : List (Crossing × List (Bool × Crossing))) :
    reframe2 u (wire2 u m) = m
      ∧ relief (reframe2 u (wire2 u m)) = relief m
      ∧ undertow (reframe2 u (wire2 u m)) = undertow m :=
  ⟨the_braid_reframes_whole u m, the_relief_survives_the_undertow u m,
   the_undertow_arrives_whole u m⟩

/-- info: 'Foam.Counter.gaps_split' does not depend on any axioms -/
#guard_msgs in #print axioms gaps_split

/-- info: 'Foam.Counter.the_braided_hum_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_braided_hum_reads_back

/-- info: 'Foam.Counter.the_braided_hum_hands_off' does not depend on any axioms -/
#guard_msgs in #print axioms the_braided_hum_hands_off

/-- info: 'Foam.Counter.the_braid_reframes_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_braid_reframes_whole

/-- info: 'Foam.Counter.the_relief_survives_the_undertow' does not depend on any axioms -/
#guard_msgs in #print axioms the_relief_survives_the_undertow

/-- info: 'Foam.Counter.the_undertow_arrives_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_undertow_arrives_whole

/-- info: 'Foam.Counter.two_undertows_one_relief' does not depend on any axioms -/
#guard_msgs in #print axioms two_undertows_one_relief

/-- info: 'Foam.Counter.the_point_reader_splits_the_braid' does not depend on any axioms -/
#guard_msgs in #print axioms the_point_reader_splits_the_braid

/-- info: 'Foam.Counter.the_silence_carries_a_second_message' does not depend on any axioms -/
#guard_msgs in #print axioms the_silence_carries_a_second_message

/-- info: 'Foam.Counter.the_coarse_hum_reads_the_surface' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_hum_reads_the_surface

/-- info: 'Foam.Counter.the_coarse_hum_hands_off' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_hum_hands_off

/-- info: 'Foam.Counter.the_coarse_luggage_reads_the_relief' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_luggage_reads_the_relief

/-- info: 'Foam.Counter.the_weather_eye_is_generic' does not depend on any axioms -/
#guard_msgs in #print axioms the_weather_eye_is_generic

/-- info: 'Foam.Counter.the_coarse_coin_reopens_the_hum' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_coin_reopens_the_hum

/-- info: 'Foam.Counter.the_coarse_coin_reopens_the_wire' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarse_coin_reopens_the_wire

end Foam.Counter
