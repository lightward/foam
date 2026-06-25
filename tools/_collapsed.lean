namespace Foam

variable {S : Type}
variable {B D : Type} (knows : D → List B → Bool) (learn : D → List B → D)
variable {State : Type}
variable {G : Type} [Mul G] [One G]

structure Ty01 (State : Type) where
  Ty20 : Type
  Ty19 : Type
  d102 : State → Ty20 → Ty19

def t001 {A : Type} : List A → List A → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ t001 xs ys

theorem t002 (a b c d : Int) : a + b + c + d = (a + c) + (b + d) := by
  rw [t005 (a + b) c d, t005 a b (c + d),
    ← t005 b c d, t004 b c, t005 c b d,
    ← t005 a c (b + d)]

theorem t003 (a b c d : Int) : a + -b + c + -d = (a + c) + -(b + d) := by
  rw [Foam.t002 a (-b) c (-d), ← t025]

def d001 (a : Int) : Int := a + a

structure Ty02 (S : Type) where
  d033    : Nat → Option S
  t138 : ∀ n, d033 n = none → d033 (n + 1) = none

structure Ty03 where
  d036 : Int
  d037 : Int

theorem t004 (a b : Int) : a + b = b + a := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => show Int.ofNat (m + n) = Int.ofNat (n + m); rw [Nat.add_comm]
    | negSucc n => rfl
  | negSucc m => cases b with
    | ofNat n => rfl
    | negSucc n => show Int.negSucc (m + n).succ = Int.negSucc (n + m).succ; rw [Nat.add_comm]
theorem t005 (a b c : Int) : a + b + c = a + (b + c) := by
  cases a with
  | ofNat p => cases b with
    | ofNat q => cases c with
      | ofNat r => show Int.ofNat (p+q+r) = Int.ofNat (p+(q+r)); rw [Nat.add_assoc]
      | negSucc r => show Int.subNatNat (p+q) (r+1) = Int.ofNat p + Int.subNatNat q (r+1); rw [t038]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.subNatNat p (q+1) + Int.ofNat r = Int.ofNat p + Int.subNatNat r (q+1)
        rw [t041 p (q+1) r, t038 p r (q+1)]
      | negSucc r =>
        show Int.subNatNat p (q+1) + Int.negSucc r = Int.ofNat p + Int.negSucc (q + r).succ
        rw [t040 p (q+1) r]
        show Int.subNatNat p (q+1+(r+1)) = Int.subNatNat p ((q+r).succ + 1)
        rw [Nat.add_right_comm q 1 (r+1)]; show Int.subNatNat p (q+(r+1)+1) = Int.subNatNat p ((q+r)+1+1)
        rw [← Nat.add_assoc q r 1]
  | negSucc p => cases b with
    | ofNat q => cases c with
      | ofNat r =>
        show Int.subNatNat q (p+1) + Int.ofNat r = Int.subNatNat (q+r) (p+1)
        rw [t041 q (p+1) r]
      | negSucc r =>
        show Int.subNatNat q (p+1) + Int.negSucc r = Int.negSucc p + Int.subNatNat q (r+1)
        rw [t040 q (p+1) r,
            t004 (Int.negSucc p) (Int.subNatNat q (r+1)), t040 q (r+1) p]
        show Int.subNatNat q (p+1+(r+1)) = Int.subNatNat q (r+1+(p+1))
        rw [Nat.add_comm (p+1) (r+1)]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.subNatNat r ((p+q).succ+1) = Int.negSucc p + Int.subNatNat r (q+1)
        rw [t004 (Int.negSucc p) (Int.subNatNat r (q+1)), t040 r (q+1) p]
        show Int.subNatNat r ((p+q).succ+1) = Int.subNatNat r (q+1+(p+1))
        rw [Nat.add_right_comm q 1 (p+1)]; show Int.subNatNat r ((p+q)+1+1) = Int.subNatNat r (q+(p+1)+1)
        rw [← Nat.add_assoc q p 1, Nat.add_comm q p]
      | negSucc r =>
        show Int.negSucc ((p+q).succ + r).succ = Int.negSucc (p + (q+r).succ).succ
        rw [show (p+q).succ + r = p + (q+r).succ from by rw [Nat.succ_add, Nat.add_succ, Nat.add_assoc]]
theorem t006 (a : Int) : (-a) + a = 0 := by
  rw [t004]; exact t008 a
theorem t007 (a b c : Int) : (a + b) * c = a * c + b * c := by
  rw [t014 (a+b) c, t015, t014 c a, t014 c b]
theorem t008 (a : Int) : a + (-a) = 0 := by
  cases a with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ k =>
      show Int.subNatNat (k+1) (k+1) = 0
      rw [t043 (Nat.le_refl _), Nat.sub_self]; rfl
  | negSucc n =>
    show Int.subNatNat (n+1) (n+1) = 0
    rw [t043 (Nat.le_refl _), Nat.sub_self]; rfl
theorem t009 (k m n : Nat) : (k + m) - (k + n) = m - n := by
  induction k with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ d ih =>
    rw [show d+1+m = (d+m)+1 from by rw [Nat.add_right_comm d 1 m],
        show d+1+n = (d+n)+1 from by rw [Nat.add_right_comm d 1 n],
        Nat.succ_sub_succ]; exact ih
theorem t010 (m k n : Nat) : (m + k) - (n + k) = m - n := by
  rw [Nat.add_comm m k, Nat.add_comm n k]; exact t009 k m n
theorem t011 (m n : Nat) : (m + n) - n = m := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, Nat.succ_sub_succ]; exact ih
theorem t012 (m n : Nat) : (m + n) - m = n := by
  rw [Nat.add_comm]; exact t011 n m
theorem t013 (a b : Int) : a + b - b = a := by
  rw [Int.sub_eq_add_neg, t005, t008, Int.add_zero]
theorem t014 (a b : Int) : a * b = b * a := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => show Int.ofNat (m * n) = Int.ofNat (n * m); rw [Nat.mul_comm]
    | negSucc n => show Int.negOfNat (m * n.succ) = Int.negOfNat (n.succ * m); rw [Nat.mul_comm]
  | negSucc m => cases b with
    | ofNat n => show Int.negOfNat (m.succ * n) = Int.negOfNat (n * m.succ); rw [Nat.mul_comm]
    | negSucc n => show Int.ofNat (m.succ * n.succ) = Int.ofNat (n.succ * m.succ); rw [Nat.mul_comm]
theorem t015 (a b c : Int) : a * (b + c) = a * b + a * c := by
  cases a with
  | ofNat p => exact t032 p b c
  | negSucc p =>
    show (-(Int.ofNat (p+1))) * (b + c) = (-(Int.ofNat (p+1))) * b + (-(Int.ofNat (p+1))) * c
    rw [t027, t027, t027, t032 (p+1) b c, t025]
theorem t016 (a b c : Int) : a * b * c = a * (b * c) := by
  cases a with
  | ofNat p => cases b with
    | ofNat q => cases c with
      | ofNat r => show Int.ofNat (p*q*r) = Int.ofNat (p*(q*r)); rw [t023]
      | negSucc r =>
        show Int.ofNat (p*q) * Int.negSucc r = Int.ofNat p * (Int.ofNat q * Int.negSucc r)
        rw [t033 (p*q) r, t033 q r, t018, t034]
        show -(Int.ofNat (p*q*(r+1))) = -(Int.ofNat (p*(q*(r+1)))); rw [t023]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.ofNat p * Int.negSucc q * Int.ofNat r = Int.ofNat p * (Int.negSucc q * Int.ofNat r)
        rw [t033 p q, t014 (Int.negSucc q) (Int.ofNat r), t033 r q,
            t027, t018, t034]
        show -(Int.ofNat (p*(q+1)*r)) = -(Int.ofNat (p*(r*(q+1)))); rw [t023, Nat.mul_comm r (q+1)]
      | negSucc r =>
        show Int.ofNat p * Int.negSucc q * Int.negSucc r = Int.ofNat p * (Int.negSucc q * Int.negSucc r)
        rw [t033 p q, t027]
        show -(Int.ofNat (p*(q+1)) * Int.negSucc r) = Int.ofNat p * (Int.negSucc q * Int.negSucc r)
        rw [t033 (p*(q+1)) r]
        show -(-(Int.ofNat (p*(q+1)*(r+1)))) = Int.ofNat p * (Int.negSucc q * Int.negSucc r)
        rw [Int.neg_neg]
        show Int.ofNat (p*(q+1)*(r+1)) = Int.ofNat p * Int.ofNat ((q+1)*(r+1))
        rw [t034, t023]
  | negSucc p =>
    show (-(Int.ofNat (p+1))) * b * c = (-(Int.ofNat (p+1))) * (b * c)
    rw [t027, t027, t027]
    apply congrArg Neg.neg
    cases b with
    | ofNat q => cases c with
      | ofNat r => show Int.ofNat ((p+1)*q*r) = Int.ofNat ((p+1)*(q*r)); rw [t023]
      | negSucc r =>
        show Int.ofNat ((p+1)*q) * Int.negSucc r = Int.ofNat (p+1) * (Int.ofNat q * Int.negSucc r)
        rw [t033 ((p+1)*q) r, t033 q r, t018, t034]
        show -(Int.ofNat ((p+1)*q*(r+1))) = -(Int.ofNat ((p+1)*(q*(r+1)))); rw [t023]
    | negSucc q => cases c with
      | ofNat r =>
        show Int.ofNat (p+1) * Int.negSucc q * Int.ofNat r = Int.ofNat (p+1) * (Int.negSucc q * Int.ofNat r)
        rw [t033 (p+1) q, t014 (Int.negSucc q) (Int.ofNat r), t033 r q,
            t027, t018, t034]
        show -(Int.ofNat ((p+1)*(q+1)*r)) = -(Int.ofNat ((p+1)*(r*(q+1)))); rw [t023, Nat.mul_comm r (q+1)]
      | negSucc r =>
        show Int.ofNat (p+1) * Int.negSucc q * Int.negSucc r = Int.ofNat (p+1) * (Int.negSucc q * Int.negSucc r)
        rw [t033 (p+1) q, t027, t033 ((p+1)*(q+1)) r, Int.neg_neg]
        show Int.ofNat ((p+1)*(q+1)*(r+1)) = Int.ofNat (p+1) * Int.ofNat ((q+1)*(r+1))
        rw [t034, t023]
theorem t017 {a b : Int} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    cases a with
    | ofNat m => cases m with
      | zero => exact Or.inl rfl
      | succ k => cases b with
        | ofNat n => cases n with
          | zero => exact Or.inr rfl
          | succ j => exact absurd h (by
              show Int.ofNat ((k+1)*(j+1)) ≠ 0
              rw [show (k+1)*(j+1) = k*(j+1)+(j+1) from Nat.succ_mul k (j+1)]
              intro hc; exact Nat.noConfusion (Int.ofNat.inj hc))
        | negSucc n => exact absurd h (by
            show Int.negOfNat ((k+1)*(n+1)) ≠ 0
            rw [show (k+1)*(n+1) = k*(n+1)+(n+1) from Nat.succ_mul k (n+1)]
            intro hc; exact Int.noConfusion hc)
    | negSucc m => cases b with
      | ofNat n => cases n with
        | zero => exact Or.inr rfl
        | succ j => exact absurd h (by
            show Int.negOfNat ((m+1)*(j+1)) ≠ 0
            rw [show (m+1)*(j+1) = m*(j+1)+(j+1) from Nat.succ_mul m (j+1)]
            intro hc; exact Int.noConfusion hc)
      | negSucc n => exact absurd h (by
          show Int.ofNat ((m+1)*(n+1)) ≠ 0
          rw [show (m+1)*(n+1) = m*(n+1)+(n+1) from Nat.succ_mul m (n+1)]
          intro hc; exact Nat.noConfusion (Int.ofNat.inj hc))
  · intro h; cases h with
    | inl ha => rw [ha, t055]
    | inr hb => rw [hb, t022]

theorem t018 (a b : Int) : a * (-b) = -(a * b) := by rw [t014 a (-b), t027, t014]
theorem t019 (a : Int) : a * (-1) = -a := by rw [t018, t020]

theorem t020 (a : Int) : a * 1 = a := by
  cases a with
  | ofNat n => show Int.ofNat (n * 1) = Int.ofNat n; rw [Nat.mul_one]
  | negSucc n => show Int.negOfNat (n.succ * 1) = Int.negSucc n; rw [Nat.mul_one]; rfl
theorem t021 (a b c : Int) : a * (b - c) = a * b - a * c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, t015, t018]
theorem t022 (a : Int) : a * 0 = 0 := by rw [t014]; exact t055 a
theorem t023 (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ d ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.left_distrib, ih]
theorem t024 (c m n : Nat) (h : n ≤ m) : c * (m - n) = c * m - c * n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [t012 n d, Nat.left_distrib c n d, t012 (c*n) (c*d)]
theorem t025 (a b : Int) : -(a + b) = -a + -b := by
  apply t026
  rw [t005, t004 (-a) (-b), ← t005 b (-b) (-a), t008, t054, t008]
theorem t026 {a b : Int} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← t005, t006, t054]
theorem t027 (a b : Int) : (-a) * b = -(a * b) := by
  cases a with
  | ofNat m =>
    cases m with
    | zero => show (0:Int) * b = -((0:Int) * b); rw [t055]; rfl
    | succ k =>
      cases b with
      | ofNat n => show Int.negOfNat ((k+1) * n) = -(Int.ofNat ((k+1)*n)); rw [Int.negOfNat_eq]
      | negSucc n => show Int.ofNat ((k+1) * n.succ) = -(Int.negOfNat ((k+1) * n.succ)); rw [Int.negOfNat_eq, Int.neg_neg]
  | negSucc m =>
    cases b with
    | ofNat n => show Int.ofNat (m.succ * n) = -(Int.negOfNat (m.succ * n)); rw [Int.negOfNat_eq, Int.neg_neg]
    | negSucc n => show Int.negOfNat (m.succ * n.succ) = -(Int.ofNat (m.succ * n.succ)); rw [Int.negOfNat_eq]
theorem t028 (a b : Nat) :
    -(Int.ofNat a) + -(Int.ofNat b) = -(Int.ofNat (a + b)) := by
  rw [← t025]; rfl
theorem t029 (a b : Nat) : -(Int.ofNat a) + Int.ofNat b = Int.subNatNat b a := by
  rw [t004, t031]
theorem t030 (a b : Int) : -(a - b) = b - a := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, t025, Int.neg_neg, t004]
theorem t031 (a b : Nat) : Int.ofNat a + -(Int.ofNat b) = Int.subNatNat a b := by
  cases b with
  | zero => show Int.ofNat a + 0 = Int.subNatNat a 0; rw [Int.add_zero, t043 (Nat.zero_le a), Nat.sub_zero]
  | succ k => show Int.ofNat a + Int.negSucc k = Int.subNatNat a (k+1); rfl
theorem t032 (p : Nat) (b c : Int) :
    Int.ofNat p * (b + c) = Int.ofNat p * b + Int.ofNat p * c := by
  cases b with
  | ofNat q => cases c with
    | ofNat r =>
      show Int.ofNat (p*(q+r)) = Int.ofNat (p*q) + Int.ofNat (p*r)
      rw [Nat.left_distrib]; rfl
    | negSucc r =>
      show Int.ofNat p * Int.subNatNat q (r+1) = Int.ofNat (p*q) + Int.ofNat p * Int.negSucc r
      rw [t035 p q (r+1), t033 p r, t031]
  | negSucc q => cases c with
    | ofNat r =>
      show Int.ofNat p * Int.subNatNat r (q+1) = Int.ofNat p * Int.negSucc q + Int.ofNat (p*r)
      rw [t035 p r (q+1), t033 p q,
          t004 (-(Int.ofNat (p*(q+1)))) (Int.ofNat (p*r)), t031]
    | negSucc r =>
      show Int.ofNat p * Int.negSucc (q + r).succ = Int.ofNat p * Int.negSucc q + Int.ofNat p * Int.negSucc r
      rw [t033 p (q+r+1), t033 p q, t033 p r,
          t028]
      show -(Int.ofNat (p * ((q+r)+1+1))) = -(Int.ofNat (p*(q+1) + p*(r+1)))
      rw [← Nat.left_distrib p (q+1) (r+1)]
      show -(Int.ofNat (p * ((q+r)+1+1))) = -(Int.ofNat (p*((q+1)+(r+1))))
      rw [show (q+1)+(r+1) = (q+r)+1+1 from by
            rw [← Nat.add_assoc (q+1) r 1, Nat.add_right_comm q 1 r]]
theorem t033 (p q : Nat) : Int.ofNat p * Int.negSucc q = -(Int.ofNat (p*(q+1))) := by
  rw [show Int.negSucc q = -(Int.ofNat (q+1)) from rfl, t018]; rfl
theorem t034 (p q : Nat) : Int.ofNat p * Int.ofNat q = Int.ofNat (p*q) := rfl
theorem t035 (c m n : Nat) :
    Int.ofNat c * Int.subNatNat m n = Int.subNatNat (c*m) (c*n) := by
  cases c with
  | zero => rw [show Int.ofNat 0 = (0:Int) from rfl, t055, Nat.zero_mul, Nat.zero_mul]; rfl
  | succ c' =>
    rcases Nat.lt_or_ge n m with hlt | hge
    · rw [t043 (Nat.le_of_lt hlt),
          t043 (Nat.mul_le_mul_left (c'+1) (Nat.le_of_lt hlt))]
      show Int.ofNat ((c'+1) * (m - n)) = Int.ofNat ((c'+1)*m - (c'+1)*n)
      rw [t024 (c'+1) m n (Nat.le_of_lt hlt)]
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt
      · rw [← heq, t043 (Nat.le_refl m), Nat.sub_self,
            t043 (Nat.le_refl ((c'+1)*m)), Nat.sub_self]; rfl
      · have hmul : (c'+1)*m < (c'+1)*n := Nat.mul_lt_mul_of_pos_left hlt (Nat.succ_pos c')
        rw [t044 hlt, t044 hmul, t018]
        show -(Int.ofNat ((c'+1) * (n - m))) = -(Int.ofNat ((c'+1)*n - (c'+1)*m))
        rw [t024 (c'+1) n m (Nat.le_of_lt hlt)]
theorem t036 (a : Nat) (s : Int) :
    Int.ofNat (a+1) + s = (Int.ofNat a + s) + 1 := by
  cases s with
  | ofNat j =>
    show Int.ofNat ((a+1)+j) = Int.ofNat (a+j) + 1
    rw [show (a+1)+j = (a+j)+1 from by rw [Nat.add_right_comm a 1 j]]; rfl
  | negSucc j =>
    show Int.subNatNat (a+1) (j+1) = Int.subNatNat a (j+1) + 1
    rw [t047 a j, t046 a j]
theorem t037 (a : Int) : 1 * a = a := by rw [t014]; exact t020 a
theorem t038 (m n k : Nat) :
    Int.subNatNat (m + n) k = Int.ofNat m + Int.subNatNat n k := by
  induction m with
  | zero => rw [Nat.zero_add, show Int.ofNat 0 = (0:Int) from rfl, t054]
  | succ a ih =>
    rw [Nat.succ_add, t045 (a+n) k, ih]
    exact (t036 a (Int.subNatNat n k)).symm
theorem t039 (m n k : Nat) :
    Int.subNatNat (m + k) (n + k) = Int.subNatNat m n := by
  show (match (n+k) - (m+k) with | 0 => Int.ofNat ((m+k) - (n+k)) | Nat.succ c => Int.negSucc c)
     = (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ c => Int.negSucc c)
  rw [t010 n k m, t010 m k n]
theorem t040 (m n k : Nat) :
    Int.subNatNat m n + Int.negSucc k = Int.subNatNat m (n + (k+1)) := by
  rcases Nat.lt_or_ge n m with hlt | hge
  · rw [t043 (Nat.le_of_lt hlt)]
    show Int.subNatNat (m-n) (k+1) = Int.subNatNat m (n+(k+1))
    obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hlt)
    rw [t012,
        show n+d = d+n from Nat.add_comm n d, show n+(k+1) = (k+1)+n from Nat.add_comm n (k+1),
        t039 d (k+1) n]
  · obtain ⟨d, rfl⟩ := Nat.le.dest hge
    rcases d with _ | d'
    · rw [Nat.add_zero, t043 (Nat.le_refl m), Nat.sub_self]
      show Int.negSucc k = Int.subNatNat m (m + (k+1))
      rw [show m+(k+1) = m+k+1 from (Nat.add_assoc m k 1).symm, t042 m k]
    · rw [show m+(d'+1) = m+d'+1 from (Nat.add_assoc m d' 1).symm, t042 m d']
      show Int.negSucc (d' + k).succ = Int.subNatNat m (m + (d'+1) + (k+1))
      rw [show m+(d'+1)+(k+1) = m + ((d'+k+1)+1) from by
            rw [Nat.add_assoc m (d'+1) (k+1)]
            apply congrArg (m + ·)
            rw [Nat.add_assoc d' 1 (k+1), Nat.add_comm 1 (k+1), ← Nat.add_assoc d' (k+1) 1,
                Nat.add_assoc d' k 1],
          show m + ((d'+k+1)+1) = m + (d'+k+1) + 1 from (Nat.add_assoc m (d'+k+1) 1).symm,
          t042 m (d'+k+1)]
theorem t041 (m n k : Nat) :
    Int.subNatNat m n + Int.ofNat k = Int.subNatNat (m + k) n := by
  rw [Nat.add_comm m k, t038 k m n, t004]
theorem t042 (m d : Nat) : Int.subNatNat m (m + d + 1) = Int.negSucc d := by
  show (match (m+d+1) - m with | 0 => Int.ofNat (m - (m+d+1)) | Nat.succ k => Int.negSucc k) = Int.negSucc d
  have h : (m + d + 1) - m = d + 1 := by rw [Nat.add_assoc m d 1, t012]
  rw [h]
theorem t043 {m n : Nat} (h : n ≤ m) : Int.subNatNat m n = Int.ofNat (m - n) := by
  show (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ k => Int.negSucc k) = Int.ofNat (m - n)
  rw [t049 h]
theorem t044 {m n : Nat} (h : m < n) : Int.subNatNat m n = -(Int.ofNat (n - m)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [show Int.subNatNat m (m+1+d) = Int.negSucc d from by
        rw [show m+1+d = m+d+1 from by rw [Nat.add_right_comm m 1 d]]; exact t042 m d]
  rw [show (m+1+d) - m = d+1 from by
        rw [Nat.add_right_comm m 1 d, Nat.add_assoc m d 1, t012]]
  rfl
theorem t045 (m k : Nat) :
    Int.subNatNat (m+1) k = Int.subNatNat m k + 1 := by
  rcases Nat.lt_or_ge k (m+1) with hlt | hge
  · have hkm : k ≤ m := Nat.le_of_lt_succ hlt
    rw [t043 (Nat.le_of_lt hlt), t043 hkm]
    obtain ⟨d, rfl⟩ := Nat.le.dest hkm
    rw [t012,
        show (k+d+1) - k = d+1 from by rw [Nat.add_assoc k d 1, t012]]
    rfl
  · obtain ⟨e, rfl⟩ := Nat.le.dest hge
    rcases e with _ | e'
    · rw [Nat.add_zero, t043 (Nat.le_refl _), Nat.sub_self]
      rw [show Int.subNatNat m (m+1) = Int.negSucc 0 from by
            have := t042 m 0; rw [Nat.add_zero] at this; exact this]
      rfl
    · rw [show (m+1)+(e'+1) = (m+1)+e'+1 from (Nat.add_assoc (m+1) e' 1).symm,
          t042 (m+1) e']
      rw [show m+1+e'+1 = m+(e'+1)+1 from by rw [Nat.add_right_comm m 1 e', Nat.add_assoc m e' 1],
          t042 m (e'+1)]
      rfl
theorem t046 (a j : Nat) :
    Int.subNatNat a (j+1) + 1 = Int.subNatNat a j := by
  rcases Nat.lt_or_ge j a with hlt | hge
  · rw [t043 hlt, t043 (Nat.le_of_lt hlt)]
    obtain ⟨d, rfl⟩ := Nat.le.dest hlt
    have e1 : j + 1 + d - (j+1) = d := t012 (j+1) d
    have e2 : j + 1 + d - j = d + 1 := by
      rw [Nat.add_assoc j 1 d, t012, Nat.add_comm 1 d]
    rw [e1, e2]; rfl
  · obtain ⟨d, rfl⟩ := Nat.le.dest hge
    rcases d with _ | d'
    · rw [Nat.add_zero]
      show Int.subNatNat a (a+1) + 1 = Int.subNatNat a a
      rw [t042 a 0, t043 (Nat.le_refl a), Nat.sub_self]; rfl
    · show Int.subNatNat a (a + (d'+1) + 1) + 1 = Int.subNatNat a (a + (d'+1))
      rw [t042 a (d'+1),
          show a + (d'+1) = a + d' + 1 from (Nat.add_assoc a d' 1).symm, t042 a d']
      rfl
theorem t047 (m n : Nat) :
    Int.subNatNat (m+1) (n+1) = Int.subNatNat m n := by
  show (match (n+1) - (m+1) with | 0 => Int.ofNat ((m+1) - (n+1)) | Nat.succ c => Int.negSucc c)
     = (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ c => Int.negSucc c)
  rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
theorem t048 (a b : Int) : a - b + b = a := by
  rw [Int.sub_eq_add_neg, t005, t006, Int.add_zero]
theorem t049 {m n : Nat} (h : m ≤ n) : m - n = 0 := by
  induction h with
  | refl => exact Nat.sub_self m
  | step _ ih => rw [Nat.sub_succ, ih]; rfl
theorem t050 (a b c : Int) : (a - b) * c = a * c - b * c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, t007, t027]
theorem t051 (a b c : Int) : a - b - c = a - (b + c) := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg, t005, t025]

theorem t052 (a : Int) : a - 0 = a := by
  rw [Int.sub_eq_add_neg]; show a + (-0) = a; rw [show (-0:Int) = 0 from rfl, Int.add_zero]
theorem t053 (a : Int) : 2 * a = a + a := by
  rw [show (2:Int) = 1 + 1 from rfl, t007, t037]
theorem t054 (a : Int) : 0 + a = a := by
  cases a with
  | ofNat n => show Int.ofNat (0 + n) = Int.ofNat n; rw [Nat.zero_add]
  | negSucc n => rfl
theorem t055 (a : Int) : 0 * a = 0 := by
  cases a with
  | ofNat n => show Int.ofNat (0 * n) = Int.ofNat 0; rw [Nat.zero_mul]
  | negSucc n => show Int.negOfNat (0 * n.succ) = (0:Int); rw [Nat.zero_mul]; rfl
structure Ty04 where
  d105 : Ty21
  d106 : Ty21

structure Ty05 where
  d043 : Int
  d041 : Int
  deriving DecidableEq

theorem Ty05.t056 (a : Int) : ∃ k : Nat, a * a = Int.ofNat k := by
  cases a with
  | ofNat m => exact ⟨m * m, rfl⟩
  | negSucc m => exact ⟨(m + 1) * (m + 1), rfl⟩

class Ty06 (G : Type) extends Mul G, One G where
  d046       : G → G
  t144   : ∀ a : G, 1 * a = a
  t143   : ∀ a : G, a * 1 = a
  t141 : ∀ a b c : G, a * b * c = a * (b * c)
  t142   : ∀ a : G, a * d046 a = 1
  t140   : ∀ a : G, d046 a * a = 1

theorem t057 (p q r s : Int) : (p + q) + (r + s) = (p + s) + (q + r) := by
  rw [t005 p q (r + s), t004 r s, ← t005 q s r,
      t004 q s, t005 s q r, ← t005 p s (q + r)]

theorem t058 (p q r s : Int) : (p + q) + (r + s) = (p + r) + (q + s) := by
  rw [t005 p q (r + s), ← t005 q r s, t004 q r,
      t005 r q s, ← t005 p r (q + s)]

theorem t059 (a b c d : Int) :
    (a * c + b * d) * (a * c + b * d)
      + (-(b * c) + a * d) * (-(b * c) + a * d)
    = (a * a + b * b) * (c * c + d * d) := by
  rw [t015 (a * c + b * d) (a * c) (b * d),
      t007 (a * c) (b * d) (a * c), t007 (a * c) (b * d) (b * d)]
  rw [t015 (-(b * c) + a * d) (-(b * c)) (a * d),
      t007 (-(b * c)) (a * d) (-(b * c)), t007 (-(b * c)) (a * d) (a * d)]
  rw [t015 (a * a + b * b) (c * c) (d * d),
      t007 (a * a) (b * b) (c * c), t007 (a * a) (b * b) (d * d)]
  rw [Foam.t064 a c, Foam.t064 b d]
  rw [Foam.t061 (b * c) (b * c), Foam.t064 b c, Foam.t064 a d]
  rw [t018 (a * d) (b * c), t027 (b * c) (a * d)]
  rw [t014 (b * d) (a * c), Foam.t060 a b c d]
  rw [Foam.t060 a b d c, t014 d c]
  rw [t014 (b * c) (a * d), Foam.t060 a b d c, t014 d c]
  exact Foam.t063 (a * a * (c * c)) (a * b * (c * d)) (b * b * (d * d))
        (b * b * (c * c)) (a * a * (d * d))

theorem t060 (a b c d : Int) : (a * c) * (b * d) = (a * b) * (c * d) := by
  rw [t016 a c (b * d), ← t016 c b d, t014 c b,
      t016 b c d, ← t016 a b (c * d)]

theorem t061 (a b : Int) : (-a) * (-b) = a * b := by
  rw [t027, t018, Int.neg_neg]

theorem t062 (a : Int) : -a * -a = a * a := by
  rw [t027, t018, Int.neg_neg]

theorem t063 (W K Z M N : Int) :
    ((W + K) + (K + Z)) + ((M + (-K)) + ((-K) + N)) = (W + M) + (N + Z) := by
  rw [Foam.t057 W K K Z, Foam.t057 M (-K) (-K) N,
      Foam.t058 (W + Z) (K + K) (M + N) ((-K) + (-K)),
      Foam.t057 K K (-K) (-K), t008 K, Int.add_zero, Int.add_zero,
      Foam.t058 W Z M N, t004 Z N]

theorem t064 (a c : Int) : (a * c) * (a * c) = (a * a) * (c * c) :=
  Foam.t060 a a c c

theorem t065 (x : Int) : 2 * x = x + x := by
  rw [show (2 : Int) = 1 + 1 from rfl, t007, t037]

structure Ty07 (A B : Type) where
  d051     : A → B
  d049     : B → A
  t146 : ∀ b, d051 (d049 b) = b
  t145 : ∀ a, d049 (d051 a) = a

def Ty08 : Nat → Type
  | 0 => PUnit
  | n + 1 => Ty08 n × Int

def Ty08.d002 : Nat → Nat := fun n => n

def Ty08.d003 [DecidableEq S] : List S → S → Nat
  | [],     _ => 0
  | x :: l, s => (if x = s then 1 else 0) + d003 l s

def Ty08.d004 (ledger : List S) : List S := ledger

def t066 : List Bool → Prop
  | [] => True
  | [_] => True
  | true :: true :: _ => False
  | _ :: ds => t066 ds

structure Ty09 where
  d053 : Ty10
  d054 : Ty10
  deriving DecidableEq

abbrev t067 : Nat → Prop := fun n => n ≤ 3

structure Ty10 where
  d056 : Ty05
  d057 : Ty05
  deriving DecidableEq

abbrev Ty11 (Handle : Type) := List (Handle × Handle)

def t068 {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) : Prop :=
  ∃ g : A → B, ∀ s p, o2 s p = g (o1 s p)

def t069 {S : Type} (r r' : S → S → Prop) : Prop := ∀ a b, r a b → r' a b

inductive Ty12 | c1 | c2 | c3 | c4
  deriving DecidableEq

def Ty13 : Nat → Type
  | 0 => Ty05
  | n + 1 => Ty13 n × Ty13 n

structure Ty14 where
  d076 : Int
  d077 : Int

structure Ty15 (A B : Type) where
  d079       : A → B
  t158 : ∀ {x y : A}, d079 x = d079 y → x = y
  t157  : ∃ y : B, ∀ x : A, d079 x ≠ y

structure Ty16 (G : Type) [Mul G] [One G] where
  Ty24     : Type
  d131     : G → Ty24 → Ty24
  t241 : ∀ p, d131 1 p = p
  t239 : ∀ g h p, d131 (g * h) p = d131 g (d131 h p)
  d133     : Ty24 → Ty24 → G
  t237 : ∀ p q, d131 (d133 q p) p = q
  t249 : ∀ g p, d133 (d131 g p) p = g

structure Ty17 where
  d081 : Ty09
  d082 : Ty09
  deriving DecidableEq

structure Ty18 where
  Ty27 : Type
  Ty26 : Type
  Ty25   : Type
  d134   : Ty27 → Ty26 → Ty25

def d005 : Nat → Int
  | 0 => 1
  | (n + 1) => -(d005 n)

theorem t070 {α : Type} :
    ∀ (as bs cs : List α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
  | [],      _,  _  => rfl
  | a :: as, bs, cs => congrArg (a :: ·) (t070 as bs cs)

theorem t071 {α : Type} : ∀ (as : List α), as ++ [] = as
  | []      => rfl
  | a :: as => congrArg (a :: ·) (t071 as)

def d006 (n : Nat) : Nat := n + 1

def d007 : Int → Nat
  | Int.ofNat _ => 0
  | Int.negSucc k => k + 1

def d008 {B : Type} (ys : List (B × B)) : List B := ys.map Prod.fst

def d009 (n : Nat) : Nat := n - 1

def d010 : Nat → Int → Int
  | 0, bal => bal
  | k + 1, bal => d010 k (d086 bal bal)

theorem t072
    (h : ∀ s t : State × Int, s.1 = t.1 → s = t) :
    ∀ s : State, ∀ n : Int, (s, n) = (s, (0 : Int)) :=
  fun s n => h (s, n) (s, 0) rfl

def d011 {B : Type} (xs : List B) : List (B × B) := xs.map (fun b => (b, b))

def d012 (s : D × List B) : List (List B) :=
  match s.2 with
  | []     => []
  | a :: l => [a :: l]

def d013 (s : D × List B) (b : B) : (D × List B) × List (List B) :=
  match knows s.1 (s.2 ++ [b]) with
  | true  => ((s.1, s.2 ++ [b]), [])
  | false => ((learn s.1 (s.2 ++ [b]), []), [s.2 ++ [b]])

def d014 : Nat → Int
  | 0 => 0
  | 1 => 1
  | (n + 2) => d014 (n + 1) + d014 n

def d015 {B W : Type} (next : List B → W → B) (out : List B) (w : W) :
    List B × List B :=
  (out ++ [next out w], [next out w])

def t073 (b : Int) : Prop := ∃ m : Nat, b = Int.ofNat m

theorem t074 (t x u v : Int) :
    (t * u - x * v) - (t * v - x * u) = (t + x) * (u - v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t * u + -(x * v)) (b := t * v + -(x * u)),
      t025 (a := t * v) (b := -(x * u)), Int.neg_neg (x * u),
      Int.sub_eq_add_neg (a := u) (b := v), t015 (t + x) u (-v),
      t007 t x u, t007 t x (-v), t018 t v, t018 x v,
      Foam.t057 (t * u) (-(x * v)) (-(t * v)) (x * u),
      t004 (-(x * v)) (-(t * v))]

theorem t075 (t x u v : Int) :
    (t * u - x * v) + (t * v - x * u) = (t - x) * (u + v) := by
  rw [Int.sub_eq_add_neg (a := t * u) (b := x * v),
      Int.sub_eq_add_neg (a := t * v) (b := x * u),
      Int.sub_eq_add_neg (a := t) (b := x), t007 t (-x) (u + v),
      t015 t u v, t015 (-x) u v, t027 x u, t027 x v,
      Foam.t058 (t * u) (-(x * v)) (t * v) (-(x * u)),
      t004 (-(x * v)) (-(x * u))]

def t076 {State Probe A : Type} (o : State → Probe → A) (s t : State) : Prop :=
  ∀ p, o s p = o t p

theorem t077 (a x y : Int) (h : a + x = a + y) : x = y := by
  have h2 : -a + (a + x) = -a + (a + y) := congrArg (-a + ·) h
  rw [← t005, ← t005, t006, t054, t054] at h2
  exact h2

theorem t078 : ∀ x : Int, x + x = 0 → x = 0
  | .ofNat 0, _ => rfl
  | .ofNat (n + 1), h => by
    have h' : Int.ofNat ((n + 1) + (n + 1)) = Int.ofNat 0 := h
    injection h' with h''
    exact Nat.noConfusion h''
  | .negSucc _, h => nomatch h

theorem t079 (t x u v : Int) :
    (t * u - x * v) * (t * u - x * v) - (t * v - x * u) * (t * v - x * u)
      = (t * t - x * x) * (u * u - v * v) := by
  rw [t082 (t * u - x * v) (t * v - x * u), t074 t x u v, t075 t x u v,
      Foam.t060 (t + x) (t - x) (u - v) (u + v),
      t014 (t + x) (t - x), ← t082 t x, ← t082 u v]

theorem t080 : ∀ (x y : Int), x * y = 1 → (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = -1)
  | Int.ofNat m, Int.ofNat n, h => by
    have h2 : Int.ofNat (m * n) = Int.ofNat 1 := h
    obtain ⟨hm, hn⟩ := t083 m n (Int.ofNat.inj h2)
    subst hm; subst hn; exact Or.inl ⟨rfl, rfl⟩
  | Int.ofNat m, Int.negSucc n, h => by
    exfalso
    have h' : Int.negOfNat (m * (n + 1)) = 1 := h
    cases hk : m * (n + 1) with
    | zero => rw [hk] at h'; exact absurd h' (by decide)
    | succ s => rw [hk] at h'; exact Int.noConfusion h'
  | Int.negSucc m, Int.ofNat n, h => by
    exfalso
    have h' : Int.negOfNat ((m + 1) * n) = 1 := h
    cases hk : (m + 1) * n with
    | zero => rw [hk] at h'; exact absurd h' (by decide)
    | succ s => rw [hk] at h'; exact Int.noConfusion h'
  | Int.negSucc m, Int.negSucc n, h => by
    have h2 : Int.ofNat ((m + 1) * (n + 1)) = Int.ofNat 1 := h
    obtain ⟨hm, hn⟩ := t083 (m + 1) (n + 1) (Int.ofNat.inj h2)
    have hm0 : m = 0 := Nat.succ.inj hm
    have hn0 : n = 0 := Nat.succ.inj hn
    subst hm0; subst hn0; exact Or.inr ⟨rfl, rfl⟩

theorem t081 (a b : Int) (h : a * a - b * b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) := by
  rw [t082 a b] at h
  have key : (a - b) = (a + b) → b = 0 := by
    intro heq
    rw [Int.sub_eq_add_neg] at heq
    have hnb : -b = b := t077 a (-b) b heq
    have hbb : b + b = 0 := by
      have hh := t008 b
      rw [hnb] at hh
      exact hh
    have hcancel : (b + b) = 0 → b = 0 := by
      intro hbb0
      have h2 : b + b = 2 * b := by rw [t053]
      rw [h2] at hbb0
      rcases t017.mp hbb0 with h20 | hb
      · exact absurd h20 (by decide)
      · exact hb
    exact hcancel hbb
  cases t080 (a - b) (a + b) h with
  | inl hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, t052] at hp
    exact Or.inl ⟨hp, hb0⟩
  | inr hpq =>
    obtain ⟨hp, hq⟩ := hpq
    have hb0 : b = 0 := key (hp.trans hq.symm)
    rw [hb0, t052] at hp
    exact Or.inr ⟨hp, hb0⟩

theorem t082 (a b : Int) : a * a - b * b = (a - b) * (a + b) := by
  rw [Int.sub_eq_add_neg (a := a * a) (b := b * b), Int.sub_eq_add_neg (a := a) (b := b),
      t007 a (-b) (a + b), t015 a a b, t015 (-b) a b,
      t027 b a, t027 b b, t014 b a,
      t005 (a * a) (a * b) (-(a * b) + -(b * b)),
      ← t005 (a * b) (-(a * b)) (-(b * b)),
      t008 (a * b), t054 (-(b * b))]

def d016 : Int → Bool
  | Int.ofNat 0 => false
  | Int.ofNat (_ + 1) => true
  | Int.negSucc _ => false

def d017 {B : Type} : List (List B) → List B
  | []      => []
  | s :: ss => s ++ d017 ss

def d018 {A : Type} [DecidableEq A] : List A → List A → List A
  | [], _ => []
  | _ :: _, [] => []
  | x :: xs, y :: ys => if x = y then x :: d018 xs ys else []

theorem t083 : ∀ (m n : Nat), m * n = 1 → m = 1 ∧ n = 1
  | 0, n, h => by rw [Nat.zero_mul] at h; exact Nat.noConfusion h
  | _ + 1, 0, h => by rw [Nat.mul_zero] at h; exact Nat.noConfusion h
  | j + 1, k + 1, h => by
    rw [Nat.mul_succ] at h
    have hle : j + 1 ≤ 1 := by
      have hx := Nat.le_add_left (j + 1) ((j + 1) * k)
      rw [h] at hx; exact hx
    have hj : j = 0 := Nat.succ.inj (Nat.le_antisymm hle (Nat.succ_le_succ (Nat.zero_le j)))
    subst hj
    rw [Nat.one_mul] at h
    exact ⟨rfl, congrArg Nat.succ (Nat.succ.inj h)⟩

def d019 {B W C : Type} (sample : Option C → W → B) (select : List B → Option C)
    (out : List B) (w : W) : B :=
  sample (select out) w

def d020 {S : Type} : List S → Nat → Option S
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: l, n + 1 => d020 l n

theorem t084 (c : Prop) [inst : Decidable c] :
    (if c then (1 : Int) else 0) = Int.ofNat (if c then 1 else 0) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem t085 (n : Nat) : Int.ofNat (n + 1) - 1 = Int.ofNat n := by
  show (Int.ofNat n + 1) - 1 = Int.ofNat n
  exact Foam.t013 (Int.ofNat n) 1

def d021 : List Bool → Nat
  | [] => 0
  | false :: ds => d021 ds
  | true :: ds => d021 ds + 1

def d022 : Int → Nat
  | Int.ofNat m => m
  | Int.negSucc _ => 0

def d023 : Bool := false
def d024 : Bool := true

def d025 {S B : Type} (step : S → B → S) (init : S) (stream : List B) : S :=
  stream.foldl step init

def d026 {S B O : Type} (step : S → B → S × List O) (init : S) : List B → List O
  | []      => []
  | b :: bs => (step init b).2 ++ d026 step (step init b).1 bs

theorem t086 : ∀ m : Nat, (Int.ofNat m) ≠ (-1 : Int) := by
  intro m h
  exact Int.noConfusion h

theorem t087 : (-1 : Int) + 1 = 0 := rfl

def d027 {C : Type} (charged : C → Bool) : List C → Option C
  | []      => none
  | c :: cs => bif charged c then some c else d027 charged cs

theorem t088 (inflow residual : Nat) : inflow - residual ≤ inflow :=
  Nat.sub_le inflow residual

def d028 : Nat → List Bool → Int
  | _, [] => 0
  | i, false :: ds => d028 (i + 1) ds
  | i, true :: ds => d014 i + d028 (i + 1) ds

def d029 : Ty18 := ⟨Int, Unit, Nat, fun b _ => d022 b⟩

def d031 : Ty12 → Ty05
  | Foam.Ty12.c1 => ⟨1, 0⟩
  | Foam.Ty12.c2 => ⟨-1, 0⟩
  | Foam.Ty12.c3 => ⟨1, 0⟩
  | Foam.Ty12.c4 => ⟨-1, 0⟩

def d032 : Ty12 → Ty05
  | _ => ⟨1, 0⟩

theorem t089 (x y : Int) : (x + y) + -(x + -y) = Foam.d001 y := by
  rw [t025, Int.neg_neg y, ← t005 (x + y) (-x) y,
    Foam.t002 x y (-x) y, t008 x, t054]
  rfl

theorem t090 (x y : Int) : (x + y) + (x + -y) = Foam.d001 x := by
  rw [← t005 (x + y) x (-y), Foam.t002 x y x (-y),
    t008 y, Int.add_zero]
  rfl

theorem t091 (a b : Int) : Foam.d001 (a + b) = Foam.d001 a + Foam.d001 b := by
  show (a + b) + (a + b) = (a + a) + (b + b)
  rw [← t005 (a + b) a b, Foam.t002 a b a b]

theorem t092 (a b : Int) : Foam.d001 (a + -b) = Foam.d001 a + -Foam.d001 b := by
  show (a + -b) + (a + -b) = (a + a) + -(b + b)
  rw [← t005 (a + -b) a (-b), Foam.t002 a (-b) a (-b), t025]

abbrev Ty21 := Ty08 3

structure Ty22 (S : Ty18) where
  t139      : S.Ty27 → S.Ty27 → Prop
  t350 : t227 S t139

def Ty05.d040 : Ty05 := ⟨0, 1⟩
def Ty05.d042 : Ty05 := ⟨1, 0⟩

def Ty05.d044 : Ty05 := ⟨0, 0⟩
theorem Ty08.t093 [DecidableEq S] {xs ys : List S} (h : xs.Perm ys) (s : S) :
    d003 xs s = d003 ys s := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg ((if x = s then 1 else 0) + ·) ih
  | swap x y l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem Ty08.t094 [DecidableEq S] (a b : S) (hab : a ≠ b) :
    ([a, b].Perm [b, a]) ∧ (∀ s, d003 [a, b] s = d003 [b, a] s)
      ∧ d004 [a, b] ≠ d004 [b, a] := by
  refine ⟨List.Perm.swap b a [], fun s => t093 (List.Perm.swap b a []) s, ?_⟩
  intro h
  injection h with ha _
  exact hab ha

def Ty08.d052 : (n : Nat) → Ty08 n
  | 0 => PUnit.unit
  | n + 1 => (Foam.Ty08.d052 n, 0)

inductive Ty23 {Handle : Type} (q : Ty11 Handle) : Handle → Handle → Type where
  | c6  {a : Handle} : Ty23 q a a
  | c5 {a b c : Handle} : ((a, b) ∈ q) → Ty23 q b c → Ty23 q a c

def Ty10.d059 : Ty10 := ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩
def Ty10.d060 : Ty10 := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
def Ty11.d061 {Handle : Type} (q : Ty11 Handle) (e : Handle × Handle) :
    Ty11 Handle := e :: q

def Ty11.d062 {Handle : Type} (q : Ty11 Handle) : Ty11 Handle :=
  q.map (fun e => (e.2, e.1))

theorem t068.t095 {State Probe A : Type} (o : State → Probe → A) :
    t068 o o :=
  ⟨fun a => a, fun _ _ => rfl⟩

theorem t068.t096 {State Probe A B C : Type}
    {o1 : State → Probe → A} {o2 : State → Probe → B} {o3 : State → Probe → C}
    (h12 : t068 o1 o2) (h23 : t068 o2 o3) : t068 o1 o3 := by
  obtain ⟨g, hg⟩ := h12
  obtain ⟨g', hg'⟩ := h23
  exact ⟨fun a => g' (g a), fun s p => by rw [hg' s p, hg s p]⟩

theorem t069.t097 {S : Type} (r : S → S → Prop) : t069 r r :=
  fun _ _ h => h

theorem t069.t098 {S : Type} {r r' r'' : S → S → Prop}
    (h1 : t069 r r') (h2 : t069 r' r'') : t069 r r'' :=
  fun a b h => h2 a b (h1 a b h)

structure t099 (bank : List (Ty01 State)) (q : Ty01 State)
    (bank' : List (Ty01 State)) : Prop where
  t148   : q ∈ bank'
  t358   : ∀ p ∈ bank', p = q ∨ ¬ q.t198 p
  t149 : ∀ p ∈ bank', p = q ∨ p ∈ bank
  t357   : ∀ p ∈ bank, p ∈ bank' ∨ q.t198 p

def Ty12.d063 : Ty12 → Ty05
  | Foam.Ty12.c1 => ⟨1, 0⟩
  | Foam.Ty12.c2 => ⟨0, 1⟩
  | Foam.Ty12.c3 => ⟨-1, 0⟩
  | Foam.Ty12.c4 => ⟨0, -1⟩

def Ty12.d065 : Ty12 → Nat
  | Foam.Ty12.c1 => 0
  | Foam.Ty12.c2 => 1
  | Foam.Ty12.c3 => 2
  | Foam.Ty12.c4 => 3

inductive t100 {State : Type} : List (Ty01 State) → List (Ty01 State) → Prop where
  | c7 : t100 [] []
  | c8 {walk bank : List (Ty01 State)} (q : Ty01 State) :
      t100 walk bank → t354 bank q → t100 (q :: walk) bank
  | c9 {walk bank bank' : List (Ty01 State)} (q : Ty01 State) :
      t100 walk bank → t426 bank q → t099 bank q bank' → t100 (q :: walk) bank'

def Ty13.d066 : (n : Nat) → Ty13 n → Ty13 n → Ty13 n
  | 0, a, b => Foam.Ty05.d108 a b
  | n + 1, x, y => (Foam.Ty13.d066 n x.1 y.1, Foam.Ty13.d066 n x.2 y.2)

def Ty13.d067 : (n : Nat) → Ty13 n → Ty13 n
  | 0, a => Foam.Ty05.d110 a
  | n + 1, x => (Foam.Ty13.d067 n x.1, Foam.Ty13.d070 n x.2)

def Ty13.d068 : (n : Nat) → DecidableEq (Ty13 n)
  | 0 => (inferInstance : DecidableEq Ty05)
  | n + 1 => fun x y =>
    @instDecidableEqProd _ _ (Foam.Ty13.d068 n) (Foam.Ty13.d068 n) x y

instance {n : Nat} : DecidableEq (Ty13 n) := Foam.Ty13.d068 n

def Ty13.d069 : (n : Nat) → Ty13 n → Ty13 n → Ty13 n
  | 0, a, b => Foam.Ty05.d112 a b
  | n + 1, x, y =>
    (Foam.Ty13.d128 n (Foam.Ty13.d069 n x.1 y.1) (Foam.Ty13.d069 n (Foam.Ty13.d067 n y.2) x.2),
     Foam.Ty13.d066 n (Foam.Ty13.d069 n y.2 x.1) (Foam.Ty13.d069 n x.2 (Foam.Ty13.d067 n y.1)))

def Ty13.d070 : (n : Nat) → Ty13 n → Ty13 n
  | 0, a => ⟨-a.d043, -a.d041⟩
  | n + 1, x => (Foam.Ty13.d070 n x.1, Foam.Ty13.d070 n x.2)

def Ty13.d071 : (n : Nat) → Ty13 n → Int
  | 0, a => Foam.Ty05.d114 a
  | n + 1, x => Foam.Ty13.d071 n x.1 + Foam.Ty13.d071 n x.2

def Ty13.d072 : (n : Nat) → Ty13 n
  | 0 => ⟨1, 0⟩
  | n + 1 => (Foam.Ty13.d072 n, Foam.Ty13.d074 n)

def Ty13.d073 (x : Ty13 1) : Ty10 := ⟨x.1, x.2⟩
def Ty13.d074 : (n : Nat) → Ty13 n
  | 0 => Foam.Ty05.d044
  | n + 1 => (Foam.Ty13.d074 n, Foam.Ty13.d074 n)

structure Ty28 (S T : Ty18) where
  d139  : S.Ty27 → T.Ty27
  d138  : S.Ty26 → T.Ty26
  d137    : S.Ty25 → T.Ty25
  t255 : ∀ s p, T.d134 (d139 s) (d138 p) = d137 (S.d134 s p)

theorem t101 {A : Type} : ∀ o : List A, t001 o o
  | [] => trivial
  | _ :: xs => ⟨rfl, t101 xs⟩

theorem t102 (rest : List Bool) :
    d021 (true :: true :: false :: rest) = d021 (false :: false :: true :: rest) + 1 := rfl

theorem t103 (i : Nat) (rest : List Bool) :
    d028 i (true :: true :: false :: rest) = d028 i (false :: false :: true :: rest) := by
  show d014 i + (d014 (i + 1) + d028 (i + 3) rest) = d014 (i + 2) + d028 (i + 3) rest
  rw [t113 i, ← t005, t004 (d014 i) (d014 (i + 1))]

def d085 : Ty01 (Nat × Int) where
  Ty20 := Unit
  Ty19 := Int
  d102 := fun s _ => d014 s.1

theorem t104 : t067 3 := by decide

theorem t105 :
    t067 3 ∧ ¬ t067 4 := by
  exact ⟨by decide, by decide⟩

def d086 (obs bal : Int) : Int :=
  match d016 obs with
  | true => bal - 1
  | false => bal

def d087 (S : Type) [DecidableEq S] : Ty18 where
  Ty27 := List S
  Ty26 := S
  Ty25   := Nat
  d134   := fun l s => Foam.Ty08.d003 l s

theorem t106 (b : Int) : d007 b = 0 ↔ t073 b := by
  cases b with
  | ofNat m => exact ⟨fun _ => ⟨m, rfl⟩, fun _ => rfl⟩
  | negSucc k =>
    constructor
    · intro h; exact Nat.noConfusion h
    · intro h; obtain ⟨m, hm⟩ := h; exact Int.noConfusion hm

def d088 : List (List B) → List B := d017

theorem t108 (k : Nat) (bal : Int) (h : t073 bal) :
    t073 (d010 k bal) := by
  induction k generalizing bal with
  | zero => exact h
  | succ n ih => exact ih (d086 bal bal) (t169 bal h)

theorem t109 (n : Nat) : d009 (d006 n) = n := rfl

theorem t110 : d009 0 = 0 := rfl

theorem t111 (n : Nat) : d009 n ≤ n := Nat.sub_le n 1

def d089 [DecidableEq S] (step : Ty05 → Ty05) : List S → S → Ty05
  | [], _ => Foam.Ty05.d044
  | x :: l, s => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step (d089 step l s))

def d090 [DecidableEq S] (step : Ty05 → Ty05) : List (Option S) → S → Ty05
  | [], _ => Foam.Ty05.d044
  | none :: l, s => step (d090 step l s)
  | some x :: l, s => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step (d090 step l s))

def d091 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) : List S → S → Ty05 → Ty05
  | [], _, z => z
  | x :: l, s, z => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step (d091 step l s z))

def d092 : Ty10 := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩
theorem t112 (n : Nat) :
    d014 (n + 1) * d014 (n + 1) - d014 (n + 2) * d014 n = d005 n := by
  induction n with
  | zero => decide
  | succ k ih =>
      have hsum : d014 (k + 2) = d014 (k + 1) + d014 k := rfl
      have hdiff : d014 (k + 2) - d014 (k + 1) = d014 k := by
        rw [hsum, Foam.t004, Foam.t013]
      show d014 (k + 2) * d014 (k + 2) - d014 (k + 3) * d014 (k + 1) = d005 (k + 1)
      rw [show d014 (k + 3) = d014 (k + 2) + d014 (k + 1) from rfl, Foam.t007,
          show d005 (k + 1) = -(d005 k) from rfl, ← ih, Foam.t030,
          ← Foam.t051, ← Foam.t021, hdiff]

theorem t113 (n : Nat) : d014 (n + 2) = d014 (n + 1) + d014 n := rfl

def d093 {S : Type} (s : S) : Ty02 S := ⟨fun _ => some s, fun _ h => nomatch h⟩

theorem t114 {B W : Type} (next : List B → W → B) :
    ∀ (out : List B) (winds : List W),
    (d026 (d015 next) out winds).length = winds.length
  | _,   []      => rfl
  | out, w :: ws => congrArg (· + 1) (t114 next (out ++ [next out w]) ws)

def d094 {A : Type} [DecidableEq A] (a b : List A) : Nat :=
  (d018 a b).length

def d095 : Int → Bool
  | Int.ofNat _ => false
  | Int.negSucc _ => true

def d096 : Nat → (Ty05 → Ty05) → Ty05 → Ty05
  | 0, _, z => z
  | n + 1, f, z => f (d096 n f z)

def d097 : Ty10 := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
theorem t115 {B : Type} :
    ∀ (xs ys : List (List B)), d017 (xs ++ ys) = d017 xs ++ d017 ys
  | [],      _  => rfl
  | s :: xs, ys =>
      (congrArg (s ++ ·) (t115 xs ys)).trans
        (t070 s (d017 xs) (d017 ys)).symm

theorem t116 (s : D × List B) : d017 (d012 s) = s.2 := by
  obtain ⟨d, cur⟩ := s
  cases cur with
  | nil      => rfl
  | cons a l => exact t071 (a :: l)

theorem t117 (m n : Nat) :
    Foam.Ty08.d002 (n + m) = Foam.Ty08.d002 n + Foam.Ty08.d002 m := rfl

theorem t118 {B : Type} : ∀ xs : List B, d008 (d011 xs) = xs
  | []      => rfl
  | x :: xs => congrArg (x :: ·) (t118 xs)

theorem t120 {A : Type} [DecidableEq A] :
    ∀ a b : List A, t001 (d018 a b) a
  | [], _ => trivial
  | _ :: _, [] => trivial
  | x :: xs, y :: ys => by
    show t001 (if x = y then x :: d018 xs ys else []) (x :: xs)
    by_cases h : x = y
    · rw [if_pos h]; exact ⟨rfl, t120 xs ys⟩
    · rw [if_neg h]; exact trivial

theorem t121 {A : Type} [DecidableEq A] :
    ∀ a b : List A, t001 (d018 a b) b
  | [], _ => trivial
  | _ :: _, [] => trivial
  | x :: xs, y :: ys => by
    show t001 (if x = y then x :: d018 xs ys else []) (y :: ys)
    by_cases h : x = y
    · rw [if_pos h]; exact ⟨h, t121 xs ys⟩
    · rw [if_neg h]; exact trivial

theorem t122 {A : Type} [DecidableEq A] : ∀ o : List A, d018 o o = o
  | [] => rfl
  | x :: xs => by
    show (if x = x then x :: d018 xs xs else []) = x :: xs
    rw [if_pos rfl, t122 xs]

theorem t123 {B W C : Type} (sample : Option C → W → B)
    (select₁ select₂ : List B → Option C) (out : List B) (w : W)
    (h : select₁ out = select₂ out) :
    d019 sample select₁ out w = d019 sample select₂ out w := by
  unfold d019; rw [h]

theorem t124 {S : Type} : ∀ s t : List S, (∀ n, d020 s n = d020 t n) → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h 0
  | _ :: _, [], h => nomatch h 0
  | a :: s, b :: t, h => by
    injection h 0 with hab
    rw [hab, t124 s t (fun n => h (n + 1))]

theorem t125 {S : Type} : ∀ l : List S, d020 l l.length = none
  | [] => rfl
  | _ :: l => t125 l

theorem t126 {S : Type} : ∀ (l : List S) (n : Nat), d020 l n = none → d020 l (n + 1) = none
  | [], _, _ => rfl
  | _ :: _, 0, h => nomatch h
  | _ :: l, n + 1, h => t126 l n h

theorem t127 (k : Nat) :
    Int.negSucc k + Int.ofNat (d007 (Int.negSucc k)) = 0 := by
  show Int.subNatNat (k + 1) (k + 1) = 0
  unfold Int.subNatNat
  rw [Nat.sub_self]
  rfl

theorem t128 {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) (h : t068 o1 o2) :
    t069 (t076 o1) (t076 o2) := by
  obtain ⟨g, hg⟩ := h
  intro s t hst p
  rw [hg s p, hg t p]
  exact congrArg g (hst p)

theorem t129 {A : Type} :
    ∀ e : List A, (∀ o : List A, t001 e o) → e = []
  | [], _ => rfl
  | _ :: _, h => (h []).elim

theorem t130 {A : Type} (o : List A) : t001 ([] : List A) o :=
  trivial

def d098 : Nat → Ty05 → Ty05
  | 0,     z => z
  | n + 1, z => Foam.Ty05.d115 (d098 n z)

def d099 {S B O : Type} (step : S → B → S × List O) : S → List B → S :=
  d025 (fun s b => (step s b).1)

theorem t131 {S B : Type} (step : S → B → S) :
    ∀ (init : S) (xs ys : List B),
    d025 step init (xs ++ ys) = d025 step (d025 step init xs) ys
  | _,    [],      _  => rfl
  | init, x :: xs, ys => t131 step (step init x) xs ys

theorem t132 {A : Type} (e : List A) (hne : e ≠ []) :
    ¬ ∀ o : List A, t001 e o :=
  fun hall => hne (t129 e hall)

theorem t133 {C : Type} (charged : C → Bool) (c : C) (cs : List C)
    (h : charged c = true) :
    d027 charged (c :: cs) = d027 charged [c] := by
  show (bif charged c then some c else d027 charged cs)
     = (bif charged c then some c else d027 charged [])
  rw [h]; rfl

theorem t134 {A : Type} [DecidableEq A] :
    ∀ e a b : List A, (t001 e a ∧ t001 e b) ↔ t001 e (d018 a b)
  | [], _, _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩
  | _ :: _, [], _ => ⟨fun ⟨h, _⟩ => h.elim, fun h => h.elim⟩
  | _ :: _, _ :: _, [] => ⟨fun ⟨_, h⟩ => h.elim, fun h => h.elim⟩
  | x :: xs, y :: ys, z :: zs => by
    show (t001 (x :: xs) (y :: ys) ∧ t001 (x :: xs) (z :: zs)) ↔
      t001 (x :: xs) (if y = z then y :: d018 ys zs else [])
    by_cases h : y = z
    · subst h
      rw [if_pos rfl]
      show ((x = y ∧ t001 xs ys) ∧ (x = y ∧ t001 xs zs)) ↔
        (x = y ∧ t001 xs (d018 ys zs))
      constructor
      · rintro ⟨⟨hxy, h1⟩, ⟨_, h2⟩⟩
        exact ⟨hxy, (t134 xs ys zs).mp ⟨h1, h2⟩⟩
      · rintro ⟨hxy, hm⟩
        obtain ⟨h1, h2⟩ := (t134 xs ys zs).mpr hm
        exact ⟨⟨hxy, h1⟩, ⟨hxy, h2⟩⟩
    · rw [if_neg h]
      exact ⟨fun ⟨⟨hxy, _⟩, ⟨hxz, _⟩⟩ => absurd (hxy.symm.trans hxz) h,
             fun h' => h'.elim⟩

def d100 [DecidableEq S] : List S → S → Ty05
  | [],     _ => Foam.Ty05.d044
  | x :: l, s => (d098 l.length (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044)).d108 (d100 l s)

theorem t135 (n : Nat) :
    ∃ l m : Ty08 n × Int, l ≠ m :=
  ⟨(Foam.Ty08.d052 n, 0), (Foam.Ty08.d052 n, 1),
   fun h => absurd (congrArg Prod.snd h) (by decide : (0 : Int) ≠ 1)⟩

def d101 : Ty18 where
  Ty27 := Unit
  Ty26 := Unit
  Ty25   := Unit
  d134   := fun _ _ => ()

theorem t136 : Foam.d031 ≠ Foam.d032 := by
  intro h
  have : Foam.d031 Foam.Ty12.c2 = Foam.d032 Foam.Ty12.c2 := by rw [h]
  exact absurd this (by decide)

def d103 : Ty12 → Ty05 := Foam.Ty12.d063

def t137 (step : Ty05 → Ty05) (n : Nat) : Prop := ∀ z, d096 n step z = z

def Ty03.d104 (z : Ty03) : Int := z.d036 * z.d036

def Ty05.d108 (z w : Ty05) : Ty05 := ⟨z.d043 + w.d043, z.d041 + w.d041⟩

def Ty05.d109 (w z : Ty05) : Int := w.d043 * z.d043 + w.d041 * z.d041
def Ty05.d110 (z : Ty05) : Ty05 := ⟨z.d043, -z.d041⟩
def Ty05.d111 (w z : Ty05) : Int := w.d043 * z.d041 - w.d041 * z.d043

def Ty05.d112 (z w : Ty05) : Ty05 :=
  ⟨z.d043 * w.d043 - z.d041 * w.d041, z.d043 * w.d041 + z.d041 * w.d043⟩

def Ty05.d113 (z : Ty05) : Ty05 := ⟨-z.d043, -z.d041⟩
def Ty05.d114 (z : Ty05) : Int := z.d043 * z.d043 + z.d041 * z.d041

def Ty05.d115 (z : Ty05) : Ty05 := ⟨-z.d041, z.d043⟩
def Ty05.d116 (z w : Ty05) : Ty05 := ⟨z.d043 - w.d043, z.d041 - w.d041⟩

def Ty23.d117 {Handle : Type} {q : Ty11 Handle} :
    {a b c : Handle} → Ty23 q a b → Ty23 q b c → Ty23 q a c
  | _, _, _, Foam.Ty23.c6,      p => p
  | _, _, _, Foam.Ty23.c5 e r, p => Foam.Ty23.c5 e (r.d117 p)

def Ty23.d119 {Handle : Type} {q : Ty11 Handle} :
    {a b : Handle} → Ty23 q a b → List (Handle × Handle)
  | _, _, Foam.Ty23.c6                 => []
  | _, _, @Foam.Ty23.c5 _ _ a b _ _ r => (a, b) :: r.d119

def Ty23.d120 {Handle : Type} {q : Ty11 Handle} :
    {a b : Handle} → Ty23 q a b → Ty23 q.d062 b a
  | _, _, Foam.Ty23.c6      => Foam.Ty23.c6
  | _, _, Foam.Ty23.c5 e r => r.d120.d117 (Foam.Ty23.c5 (t182 e) Foam.Ty23.c6)

def Ty10.d121 (x : Ty10) : Ty10 := ⟨⟨-x.d056.d043, -x.d056.d041⟩, ⟨-x.d057.d043, -x.d057.d041⟩⟩

def Ty10.d122 (q : Ty10) : Ty13 1 := (q.d056, q.d057)

def Ty10.d123 : Ty10 := ⟨Foam.Ty05.d044, Foam.Ty05.d044⟩
theorem Ty11.t147 {Handle : Type} :
    ∀ (q : Ty11 Handle), q.d062.d062 = q
  | []      => rfl
  | e :: es => congrArg (e :: ·) (Foam.Ty11.t147 es)

theorem Ty12.t150 : (Foam.Ty12.c2 * Foam.Ty12.c2 * Foam.Ty12.c2 * Foam.Ty12.c2 : Ty12) = 1 := by decide

theorem Ty12.t151 : (Foam.Ty12.c2 * Foam.Ty12.c2 : Ty12) ≠ 1 := by decide

def Ty12.d125 (k : Nat) : Ty12 :=
  match k % 4 with
  | 0 => Foam.Ty12.c1
  | 1 => Foam.Ty12.c2
  | 2 => Foam.Ty12.c3
  | _ => Foam.Ty12.c4

def Ty13.d127 (n : Nat) (x : Ty13 n) : Ty13 (n + 1) := (x, Foam.Ty13.d074 n)

theorem Ty13.t156 : (n : Nat) → Foam.Ty13.d072 n ≠ Foam.Ty13.d074 n
  | 0 => by decide
  | n + 1 => fun h => Foam.Ty13.t156 n (congrArg Prod.fst h)

def Ty13.d128 (n : Nat) (x y : Ty13 n) : Ty13 n :=
  Foam.Ty13.d066 n x (Foam.Ty13.d070 n y)

def Ty13.d129 (x : Ty13 2) : Ty09 := ⟨Foam.Ty13.d073 x.1, Foam.Ty13.d073 x.2⟩
def Ty14.d130 (z : Ty14) : Int := z.d076 * z.d076 - z.d077 * z.d077

theorem Ty15.t159 {A B : Type} (S : Ty15 A B) :
    ¬ ∃ g : B → A, ∀ b, S.d079 (g b) = b := by
  rintro ⟨g, hg⟩
  obtain ⟨y, hy⟩ := S.t157
  exact hy (g y) (hg y)

def Ty15.t160 {A B : Type} (S : Ty15 A B) (q : B) : Prop := ∀ x : A, S.d079 x ≠ q

def Ty16.d132 (S : Ty16 G) : List G → S.Ty24 → S.Ty24
  | [], p => p
  | g :: rest, p => S.d132 rest (S.d131 g p)

def Ty28.d136 (S : Ty18) : Ty28 S S where
  d139  := fun s => s
  d138  := fun p => p
  d137    := fun a => a
  t255 := fun _ _ => rfl

def d140 (κ : Int) (w z : Ty05) : Int := w.d043 * z.d043 - κ * (w.d041 * z.d041)

theorem t161 (obs : Int) (m : Nat) :
    t073 (d086 obs (Int.ofNat (m + 1))) := by
  cases obs with
  | ofNat n =>
    cases n with
    | zero => exact ⟨m + 1, rfl⟩
    | succ _ => exact ⟨m, t085 m⟩
  | negSucc _ => exact ⟨m + 1, rfl⟩

def d141 (obs bal : Int) : Int :=
  match d095 obs with
  | true => bal + 1
  | false => bal

theorem t162 {S : Type} [DecidableEq S] (new old : List S) (s : S) :
    d089 id (new ++ old) s = d091 id new s (d089 id old s) :=
  t197 id new old s

def d142 (w z : Ty05) : Int := w.d043 * z.d041 - w.d041 * z.d043

theorem t163 {Handle : Type} (q : Ty11 Handle) (e : Handle × Handle) :
    (q.d061 e).length = q.length + 1 := rfl

theorem t164 : ∃ b : Int, d022 (d086 b b) ≠ d022 b :=
  ⟨1, fun h => Nat.noConfusion h⟩

theorem t165 : (Foam.Ty12.c2 * Foam.Ty12.c2 : Ty12) ≠ 1 := Foam.Ty12.t151

theorem t166 :
    ∀ (s : D × List B) (ys : List B),
    d017 (d026 (d013 knows learn) s ys)
        ++ (d099 (d013 knows learn) s ys).2
      = s.2 ++ ys
  | s, []      => (t071 s.2).symm
  | s, b :: bs => by
      cases hk : knows s.1 (s.2 ++ [b]) with
      | true =>
        have e : d013 knows learn s b = ((s.1, s.2 ++ [b]), []) := by
          unfold d013; rw [hk]
        show d017 ((d013 knows learn s b).2
                ++ d026 (d013 knows learn) (d013 knows learn s b).1 bs)
              ++ (d099 (d013 knows learn) (d013 knows learn s b).1 bs).2
            = s.2 ++ (b :: bs)
        rw [e]
        show d017 (d026 (d013 knows learn) (s.1, s.2 ++ [b]) bs)
              ++ (d099 (d013 knows learn) (s.1, s.2 ++ [b]) bs).2
            = s.2 ++ (b :: bs)
        rw [t166 (s.1, s.2 ++ [b]) bs]
        show (s.2 ++ [b]) ++ bs = s.2 ++ (b :: bs)
        exact t070 s.2 [b] bs
      | false =>
        have e : d013 knows learn s b
            = ((learn s.1 (s.2 ++ [b]), []), [s.2 ++ [b]]) := by
          unfold d013; rw [hk]
        show d017 ((d013 knows learn s b).2
                ++ d026 (d013 knows learn) (d013 knows learn s b).1 bs)
              ++ (d099 (d013 knows learn) (d013 knows learn s b).1 bs).2
            = s.2 ++ (b :: bs)
        rw [e]
        show (s.2 ++ [b])
              ++ d017 (d026 (d013 knows learn) (learn s.1 (s.2 ++ [b]), []) bs)
              ++ (d099 (d013 knows learn) (learn s.1 (s.2 ++ [b]), []) bs).2
            = s.2 ++ (b :: bs)
        rw [t070 (s.2 ++ [b]), t166 (learn s.1 (s.2 ++ [b]), []) bs]
        show (s.2 ++ [b]) ++ bs = s.2 ++ (b :: bs)
        exact t070 s.2 [b] bs

theorem t167 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) :
    ∀ (l : List S) (s : S), d089 step l s = d091 step l s Foam.Ty05.d044
  | [], _ => rfl
  | x :: l, s =>
      congrArg (fun z => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step z))
        (t167 step l s)

theorem t168 [DecidableEq S] (l : List S) (s : S) :
    d089 id l s = ⟨Int.ofNat (Foam.Ty08.d003 l s), 0⟩ := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (d089 id l s) = _
    rw [ih, t173 (x = s), t084 (x = s)]
    rfl

def d143 (S : Ty18) : Ty28 S d101 where
  d139  := fun _ => ()
  d138  := fun _ => ()
  d137    := fun _ => ()
  t255 := fun _ _ => rfl

def d144 : Ty21 := (Foam.Ty08.d052 2, (0 : Int))
def d145 : Ty21 := (Foam.Ty08.d052 2, (1 : Int))

theorem t169 (bal : Int) (h : t073 bal) :
    t073 (d086 bal bal) := by
  obtain ⟨m, rfl⟩ := h
  cases m with
  | zero => exact ⟨0, rfl⟩
  | succ k => exact ⟨k, t085 k⟩

def d146 (v : Int) (z : Ty03) : Ty03 := ⟨z.d036, v * z.d036 + z.d037⟩

theorem t170 {B W : Type} (next : List B → W → B) :
    ∀ (out : List B) (winds : List W),
    d099 (d015 next) out winds = out ++ d026 (d015 next) out winds
  | out, []      => (t071 out).symm
  | out, w :: ws =>
      (t170 next (out ++ [next out w]) ws).trans
        (t070 out [next out w] (d026 (d015 next) (out ++ [next out w]) ws))

theorem t171 {B W : Type} (next : List B → W → B)
    (out : List B) (xs ys : List W) :
    d026 (d015 next) out (xs ++ ys)
      = d026 (d015 next) out xs
        ++ d026 (d015 next) (d099 (d015 next) out xs) ys :=
  t188 (d015 next) out xs ys

def d147 (w z : Ty14) : Int := w.d076 * z.d076 - w.d077 * z.d077

def d148 (w z : Ty14) : Int := w.d076 * z.d077 - w.d077 * z.d076

theorem t172 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) (s : S) (z : Ty05) :
    d091 step [] s z = z := rfl

theorem t173 (c : Prop) [inst : Decidable c] :
    (if c then Foam.Ty05.d042 else Foam.Ty05.d044) = (⟨if c then (1 : Int) else 0, 0⟩ : Ty05) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem t174 (f : Ty05 → Ty05) :
    ∀ (n : Nat) (z : Ty05),
      d096 n (fun w => f (f w)) z = d096 n f (d096 n f z)
  | 0, _ => rfl
  | n + 1, z => by
      show f (f (d096 n (fun w => f (f w)) z))
         = f (d096 n f (f (d096 n f z)))
      rw [t174 f n z, t177 f n (d096 n f z)]

theorem t175 (f g : Ty05 → Ty05) (h : ∀ w, f w = g w) :
    ∀ (n : Nat) (z : Ty05), d096 n f z = d096 n g z
  | 0, _ => rfl
  | n + 1, z => by
      show f (d096 n f z) = g (d096 n g z)
      rw [t175 f g h n z, h (d096 n g z)]

theorem t176 : ∀ (n : Nat) (z : Ty05), d096 n (fun w => w) z = z
  | 0, _ => rfl
  | n + 1, z => t176 n z

theorem t177 (f : Ty05 → Ty05) :
    ∀ (n : Nat) (z : Ty05), d096 n f (f z) = f (d096 n f z)
  | 0, _ => rfl
  | n + 1, z => congrArg f (t177 f n z)

theorem t178 : d097.d057 ≠ Foam.Ty05.d044 := by decide

theorem t181 (obs : Int) :
    d086 obs (Int.ofNat 0) = Int.ofNat 0 ∨
      d086 obs (Int.ofNat 0) = Int.negSucc 0 := by
  cases obs with
  | ofNat n =>
    cases n with
    | zero => exact Or.inl rfl
    | succ _ => exact Or.inr rfl
  | negSucc _ => exact Or.inl rfl

theorem t182 {Handle : Type} {q : Ty11 Handle} {a b : Handle}
    (h : (a, b) ∈ q) : (b, a) ∈ q.d062 := by
  induction h with
  | head as     => exact List.Mem.head _
  | tail e _ ih => exact List.Mem.tail _ ih

def d149 (κ : Int) (z : Ty05) : Int := z.d043 * z.d043 - κ * (z.d041 * z.d041)

def d150 {S B O : Type} (step : S → B → S × List O) (flush : S → List O)
    (init : S) (stream : List B) : List O :=
  d026 step init stream ++ flush (d099 step init stream)

def d151 (S : Type) [DecidableEq S] : Ty22 (d087 S) where
  t139      := fun l l' => l.Perm l'
  t350 := fun _ _ h s => Foam.Ty08.t093 h s

def d152 {S : Type} (l : List S) : Ty02 S := ⟨d020 l, t126 l⟩

theorem t183 [DecidableEq S] (l : List (Option S)) (s : S) :
    d090 id (none :: l) s = d090 id l s := rfl

theorem t184 [DecidableEq S] (step : Ty05 → Ty05) (l : List (Option S)) (s : S) :
    d090 step (none :: l) s = step (d090 step l s) := rfl

theorem t185 (k : Nat) (z : Ty05) : d098 (k + 4) z = d098 k z := by
  rw [← t186 k 4 z, t187]

theorem t186 (m n : Nat) (z : Ty05) :
    d098 m (d098 n z) = d098 (m + n) z := by
  induction m with
  | zero =>
    show d098 n z = d098 (0 + n) z
    rw [Nat.zero_add]
  | succ k ih =>
    show Foam.Ty05.d115 (d098 k (d098 n z)) = d098 (Nat.succ k + n) z
    rw [ih, Nat.succ_add]
    rfl

theorem t187 (z : Ty05) : d098 4 z = z := by
  show z.d115.d115.d115.d115 = z
  exact Foam.Ty05.t214 z

theorem t188 {S B O : Type} (step : S → B → S × List O) :
    ∀ (init : S) (xs ys : List B),
    d026 step init (xs ++ ys)
      = d026 step init xs ++ d026 step (d099 step init xs) ys
  | _,    [],      _  => rfl
  | init, x :: xs, ys =>
      (congrArg ((step init x).2 ++ ·) (t188 step (step init x).1 xs ys)).trans
        (t070 (step init x).2
          (d026 step (step init x).1 xs)
          (d026 step (d099 step (step init x).1 xs) ys)).symm

theorem t189 {S B O : Type} (step : S → B → S × List O)
    (init : S) (xs ys : List B) :
    d099 step init (xs ++ ys) = d099 step (d099 step init xs) ys :=
  t131 (fun s b => (step s b).1) init xs ys

theorem t190 :
    Foam.Ty13.d069 1 (⟨Foam.Ty05.d044, ⟨1, 0⟩⟩ : Ty13 1) (⟨Foam.Ty05.d044, ⟨1, 0⟩⟩ : Ty13 1)
      = Foam.Ty13.d070 1 (⟨⟨1, 0⟩, Foam.Ty05.d044⟩ : Ty13 1) := rfl

theorem t191 :
    ∃ x : Ty13 3, x ≠ Foam.Ty13.d074 3 :=
  ⟨Foam.Ty13.d072 3, Foam.Ty13.t156 3⟩

theorem t192 (k : Nat) :
    d086 (Int.negSucc k) (Int.negSucc k) = Int.negSucc k := rfl

theorem t193 : d086 1 (d086 1 1) = -1 := rfl

theorem t194 : d086 2 (d086 2 2) = 0 := rfl

theorem t195 (m : Nat) :
    t073 (d086 (Int.ofNat (m + 2))
      (d086 (Int.ofNat (m + 2)) (Int.ofNat (m + 2)))) := by
  refine ⟨m, ?_⟩
  have h1 : d086 (Int.ofNat (m + 2)) (Int.ofNat (m + 2)) = Int.ofNat (m + 1) :=
    t085 (m + 1)
  rw [h1]
  exact t085 m

theorem t197 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) :
    ∀ (new old : List S) (s : S),
      d089 step (new ++ old) s = d091 step new s (d089 step old s)
  | [], _, _ => rfl
  | x :: new, old, s =>
      congrArg (fun z => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step z))
        (t197 step new old s)

def d153 (S : Ty18) (s : S.Ty27) : List S.Ty26 → List S.Ty25
  | [] => []
  | p :: ps => S.d134 s p :: d153 S s ps

def d154 (S : Ty18) (m : S.Ty27 → S.Ty27) :
    S.Ty27 → List S.Ty26 → List S.Ty25
  | _, [] => []
  | s, p :: ps => S.d134 (m s) p :: d154 S m (m s) ps

def Ty01.t198 (a b : Ty01 State) : Prop :=
  ∃ (enc : b.Ty20 → a.Ty20) (post : a.Ty19 → b.Ty19),
    ∀ s p, b.d102 s p = post (a.d102 s (enc p))

def Ty01.d155 (b : Ty01 State) : Ty01 (State × Int) where
  Ty20 := b.Ty20
  Ty19 := b.Ty19
  d102 := fun s p => b.d102 s.1 p

def Ty01.d156 (b : Ty01 State) (n : Nat) : Ty01 (State × Ty08 n) where
  Ty20 := b.Ty20
  Ty19 := b.Ty19
  d102 := fun s p => b.d102 s.1 p

def Ty01.d157 (b : Ty01 (State × Int)) : Ty01 State where
  Ty20 := b.Ty20
  Ty19 := b.Ty19
  d102 := fun s p => b.d102 (s, 0) p

def Ty01.d158 {S : Type} (b : Ty01 (S × Int)) (target : Int) :
    Ty01 (S × Int) where
  Ty20 := Option b.Ty20
  Ty19 := b.Ty19 ⊕ Bool
  d102 := fun s p =>
    match p with
    | none => Sum.inr (decide (s.2 = target))
    | some q => Sum.inl (b.d102 s q)

def Ty01.d159 {State : Type} (a b : Ty01 State) : Ty01 State where
  Ty20 := a.Ty20 × b.Ty20
  Ty19 := a.Ty19 × b.Ty19
  d102 s pq := (a.d102 s pq.1, b.d102 s pq.2)

def Ty01.d160 {State : Type} (b : Ty01 State) : Ty01 (State × Ty05) where
  Ty20 := b.Ty20
  Ty19   := b.Ty19
  d102   := fun s p => b.d102 s.1 p

def Ty01.d161 {State : Type} (b : Ty01 State) : Ty18 where
  Ty27 := State
  Ty26 := b.Ty20
  Ty25 := b.Ty19
  d134 := b.d102

theorem t199 (a b : Ty12) :
    Foam.d031 (a * b) = Foam.Ty05.d112 (Foam.d031 a) (Foam.d031 b) := by
  cases a <;> cases b <;> decide

theorem t200 (a : Ty12) : (Foam.d031 a).d114 = 1 := by
  cases a <;> decide

def d162 : Ty12 → Ty05 := fun a => Foam.Ty05.d110 (Foam.Ty12.d063 a)

theorem t201 (a b : Ty12) :
    Foam.d103 (a * b) = Foam.Ty05.d112 (Foam.d103 a) (Foam.d103 b) := by
  cases a <;> cases b <;> decide

theorem t202 (a : Ty12) : (Foam.d103 a).d114 = 1 := by
  cases a <;> decide

theorem t203 (a b : Ty12) :
    Foam.d032 (a * b) = Foam.Ty05.d112 (Foam.d032 a) (Foam.d032 b) := by
  cases a <;> cases b <;> decide

theorem t204 (a : Ty12) : (Foam.d032 a).d114 = 1 := by
  cases a <;> decide

def d163 (n0 n1 n2 n3 : Int) (f : Ty12 → Ty05) : Ty05 :=
  Foam.Ty05.d108
    (Foam.Ty05.d108 (Foam.Ty05.d112 ⟨n0, 0⟩ (f Foam.Ty12.c1)) (Foam.Ty05.d112 ⟨n1, 0⟩ (f Foam.Ty12.c2)))
    (Foam.Ty05.d108 (Foam.Ty05.d112 ⟨n2, 0⟩ (f Foam.Ty12.c3)) (Foam.Ty05.d112 ⟨n3, 0⟩ (f Foam.Ty12.c4)))

def d164 (f g : Ty12 → Ty05) : Ty05 :=
  Foam.Ty05.d108
    (Foam.Ty05.d108 (Foam.Ty05.d112 (f Foam.Ty12.c1) (Foam.Ty05.d110 (g Foam.Ty12.c1))) (Foam.Ty05.d112 (f Foam.Ty12.c2) (Foam.Ty05.d110 (g Foam.Ty12.c2))))
    (Foam.Ty05.d108 (Foam.Ty05.d112 (f Foam.Ty12.c3) (Foam.Ty05.d110 (g Foam.Ty12.c3))) (Foam.Ty05.d112 (f Foam.Ty12.c4) (Foam.Ty05.d110 (g Foam.Ty12.c4))))

def t205 (op : Ty04 → Ty04) (b : Ty01 Ty04) : Prop :=
  ∃ f p, b.d102 (op f) p ≠ b.d102 f p

theorem Ty05.t206 (θ a b : Ty05) :
    Foam.Ty05.d109 θ (Foam.Ty05.d108 a b) = Foam.Ty05.d109 θ a + Foam.Ty05.d109 θ b := by
  show θ.d043 * (a.d043 + b.d043) + θ.d041 * (a.d041 + b.d041)
     = (θ.d043 * a.d043 + θ.d041 * a.d041) + (θ.d043 * b.d043 + θ.d041 * b.d041)
  rw [t015, t015]
  exact Foam.t058 (θ.d043 * a.d043) (θ.d043 * b.d043) (θ.d041 * a.d041) (θ.d041 * b.d041)

theorem Ty05.t207 (w z : Ty05) : Foam.Ty05.d109 w (Foam.Ty05.d113 z) = -(Foam.Ty05.d109 w z) := by
  show w.d043 * (-z.d043) + w.d041 * (-z.d041) = -(w.d043 * z.d043 + w.d041 * z.d041)
  rw [t018, t018, ← t025]

def Ty05.d165 (w z : Ty05) : Int := Foam.Ty05.d109 w z * Foam.Ty05.d109 w z

theorem Ty05.t208 (θ z : Ty05) :
    Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z)
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z))
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = 0 := by
  have e3 : Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z)) = -(Foam.Ty05.d109 θ z) := by
    rw [Foam.Ty05.t216, Foam.Ty05.t207]
  have e4 : Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = -(Foam.Ty05.d109 θ (Foam.Ty05.d115 z)) := by
    rw [Foam.Ty05.t216 (Foam.Ty05.d115 z), Foam.Ty05.t207]
  rw [e3, e4,
      t005 (Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z))
        (-(Foam.Ty05.d109 θ z)) (-(Foam.Ty05.d109 θ (Foam.Ty05.d115 z))),
      Foam.t058 (Foam.Ty05.d109 θ z) (Foam.Ty05.d109 θ (Foam.Ty05.d115 z))
        (-(Foam.Ty05.d109 θ z)) (-(Foam.Ty05.d109 θ (Foam.Ty05.d115 z))),
      t008, t008, Int.add_zero]

theorem Ty05.t209 (n : Int) (w : Ty05) :
    Foam.Ty05.d112 ⟨n, 0⟩ w = ⟨n * w.d043, n * w.d041⟩ := by
  show (Foam.Ty05.mk (n * w.d043 - 0 * w.d041) (n * w.d041 + 0 * w.d043)) = ⟨n * w.d043, n * w.d041⟩
  rw [t055, t052, t055, Int.add_zero]

theorem Ty05.t210 (z : Ty05) : Foam.Ty05.d113 (Foam.Ty05.d113 z) = z := by
  cases z with
  | mk a b =>
    show (⟨- -a, - -b⟩ : Ty05) = ⟨a, b⟩
    rw [Int.neg_neg, Int.neg_neg]

theorem Ty05.t211 (z : Ty05) : z.d110.d114 = z.d114 := by
  show z.d043 * z.d043 + -z.d041 * -z.d041 = z.d043 * z.d043 + z.d041 * z.d041
  rw [Foam.t062 z.d041]

theorem Ty05.t212 (z w : Ty05) :
    (z.d112 w).d114 = z.d114 * w.d114 := by
  show (z.d043 * w.d043 - z.d041 * w.d041) * (z.d043 * w.d043 - z.d041 * w.d041)
      + (z.d043 * w.d041 + z.d041 * w.d043) * (z.d043 * w.d041 + z.d041 * w.d043)
    = (z.d043 * z.d043 + z.d041 * z.d041) * (w.d043 * w.d043 + w.d041 * w.d041)
  have L := Foam.t059 z.d043 (-z.d041) w.d043 w.d041
  rw [t027 z.d041 w.d041, t027 z.d041 w.d043, Int.neg_neg,
      Foam.t062 z.d041, ← Int.sub_eq_add_neg,
      t004 (z.d041 * w.d043) (z.d043 * w.d041)] at L
  exact L

theorem Ty05.t213 (z : Ty05) : ∃ k : Nat, z.d114 = Int.ofNat k := by
  obtain ⟨k1, h1⟩ := Foam.Ty05.t056 z.d043
  obtain ⟨k2, h2⟩ := Foam.Ty05.t056 z.d041
  refine ⟨k1 + k2, ?_⟩
  show z.d043 * z.d043 + z.d041 * z.d041 = Int.ofNat (k1 + k2)
  rw [h1, h2]; rfl

theorem Ty05.t214 (z : Ty05) :
    Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = z := Foam.Ty05.t210 z

theorem Ty05.t215 {z w : Ty05} (h : Foam.Ty05.d115 z = Foam.Ty05.d115 w) : z = w := by
  have c3 := congrArg Foam.Ty05.d115 (congrArg Foam.Ty05.d115 (congrArg Foam.Ty05.d115 h))
  rw [Foam.Ty05.t214, Foam.Ty05.t214] at c3
  exact c3

theorem Ty05.t216 (z : Ty05) : Foam.Ty05.d115 (Foam.Ty05.d115 z) = Foam.Ty05.d113 z := rfl

def t217 (S : Ty18) (m : S.Ty27 → S.Ty27) : Prop :=
  ∀ s p, S.d134 (m s) p = S.d134 s p

def Ty09.d166 : Ty09 := ⟨Foam.Ty10.d059, Foam.Ty10.d123⟩

def Ty09.d167 (o : Ty09) : Ty13 2 := (Foam.Ty10.d122 o.d053, Foam.Ty10.d122 o.d054)

def Ty09.d168 : Ty09 := ⟨Foam.Ty10.d123, Foam.Ty10.d123⟩
theorem Ty23.t218 {Handle : Type} {q : Ty11 Handle} :
    {a b c d : Handle} → (p : Ty23 q a b) → (r : Ty23 q b c) → (s : Ty23 q c d) →
    (p.d117 r).d117 s = p.d117 (r.d117 s)
  | _, _, _, _, Foam.Ty23.c6,      _, _ => rfl
  | _, _, _, _, Foam.Ty23.c5 e p, r, s => congrArg (Foam.Ty23.c5 e) (Foam.Ty23.t218 p r s)

theorem Ty23.t219 {Handle : Type} {q : Ty11 Handle} {a b : Handle}
    (p : Ty23 q a b) : p.d117 Foam.Ty23.c6 = p := by
  induction p with
  | c6 => rfl
  | c5 e r ih => exact congrArg (Foam.Ty23.c5 e) ih

theorem Ty23.t221 {Handle : Type} {q : Ty11 Handle} :
    {a b c : Handle} → (p : Ty23 q a b) → (r : Ty23 q b c) →
    (p.d117 r).d119 = p.d119 ++ r.d119
  | _, _, _, Foam.Ty23.c6,                 _ => rfl
  | _, _, _, @Foam.Ty23.c5 _ _ a b _ _ p, r =>
      congrArg ((a, b) :: ·) (Foam.Ty23.t221 p r)

theorem Ty23.t223 {Handle : Type} {q : Ty11 Handle} {a b : Handle}
    (p : Ty23 q a b) : Foam.Ty23.c6.d117 p = p := rfl

theorem Ty23.t224 {Handle : Type} {q : Ty11 Handle} :
    {a b c : Handle} → (p : Ty23 q a b) → (r : Ty23 q b c) →
    (p.d117 r).d120 = r.d120.d117 p.d120
  | _, _, _, Foam.Ty23.c6,      r => (Foam.Ty23.t219 r.d120).symm
  | _, _, _, Foam.Ty23.c5 e p, r => by
      have ih := Foam.Ty23.t224 p r
      show (p.d117 r).d120.d117 (Foam.Ty23.c5 (t182 e) Foam.Ty23.c6)
         = r.d120.d117 (p.d120.d117 (Foam.Ty23.c5 (t182 e) Foam.Ty23.c6))
      rw [ih]
      exact Foam.Ty23.t218 r.d120 p.d120 _

theorem Ty23.t225 {Handle : Type} {q : Ty11 Handle} {a : Handle} :
    (Foam.Ty23.c6 : Ty23 q a a).d120 = Foam.Ty23.c6 := rfl

def Ty10.d170 (x y : Ty10) : Ty10 := ⟨Foam.Ty05.d108 x.d056 y.d056, Foam.Ty05.d108 x.d057 y.d057⟩
def Ty10.d171 (x : Ty10) : Ty10 := ⟨Foam.Ty05.d110 x.d056, ⟨-x.d057.d043, -x.d057.d041⟩⟩
def Ty10.d172 (x y : Ty10) : Ty10 :=
  ⟨Foam.Ty05.d116 (Foam.Ty05.d112 x.d056 y.d056) (Foam.Ty05.d112 (Foam.Ty05.d110 y.d057) x.d057),
   Foam.Ty05.d108 (Foam.Ty05.d112 y.d057 x.d056) (Foam.Ty05.d112 x.d057 (Foam.Ty05.d110 y.d056))⟩

def Ty10.d173 (x y : Ty10) : Ty10 := ⟨Foam.Ty05.d116 x.d056 y.d056, Foam.Ty05.d116 x.d057 y.d057⟩

theorem Ty10.t226 (x : Ty13 1) : Foam.Ty10.d122 (Foam.Ty13.d073 x) = x := rfl

def t227 (S : Ty18) (r : S.Ty27 → S.Ty27 → Prop) : Prop :=
  ∀ s t, r s t → ∀ p, S.d134 s p = S.d134 t p

theorem Ty12.t228 (a b : Ty12) : (a * b).d063 = Foam.Ty05.d112 a.d063 b.d063 := by
  cases a <;> cases b <;> decide

theorem Ty12.t229 (a : Ty12) : (Foam.Ty12.c2 * a).d063 = Foam.Ty05.d112 Foam.Ty05.d040 a.d063 := by
  cases a <;> decide

theorem Ty12.t230 (a : Ty12) : a.d063.d114 = 1 := by
  cases a <;> decide

def Ty12.d174 (a : Ty12) : Ty12 := Foam.Ty12.d125 (4 - a.d065)

instance : Mul Ty12 := ⟨Foam.Ty12.d175⟩
instance : One Ty12 := ⟨Foam.Ty12.c1⟩

instance : Ty06 Ty12 where
  d046       := Foam.Ty12.d174
  t144   := by intro a; cases a <;> decide
  t143   := by intro a; cases a <;> decide
  t141 := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  t142   := by intro a; cases a <;> decide
  t140   := by intro a; cases a <;> decide

def Ty12.d175 (a b : Ty12) : Ty12 := Foam.Ty12.d125 (a.d065 + b.d065)
theorem Ty13.t232 (a b : Ty05) : Foam.Ty13.d069 0 a b = Foam.Ty05.d112 a b := rfl

theorem Ty13.t233 (n : Nat) {x y : Ty13 n}
    (h : Foam.Ty13.d127 n x = Foam.Ty13.d127 n y) : x = y :=
  congrArg Prod.fst h

theorem Ty13.t234 (n : Nat) :
    ∃ y : Ty13 (n + 1), ∀ x : Ty13 n, Foam.Ty13.d127 n x ≠ y :=
  ⟨(Foam.Ty13.d074 n, Foam.Ty13.d072 n), fun _ h => Foam.Ty13.t156 n (congrArg Prod.snd h).symm⟩

theorem Ty13.t235 (n : Nat) (x y : Ty13 (n + 1)) :
    Foam.Ty13.d069 (n + 1) x y =
      (Foam.Ty13.d128 n (Foam.Ty13.d069 n x.1 y.1) (Foam.Ty13.d069 n (Foam.Ty13.d067 n y.2) x.2),
       Foam.Ty13.d066 n (Foam.Ty13.d069 n y.2 x.1) (Foam.Ty13.d069 n x.2 (Foam.Ty13.d067 n y.1))) := rfl

theorem Ty13.t236 (q : Ty10) : Foam.Ty13.d073 (Foam.Ty10.d122 q) = q := rfl
def Ty13.d180 (x : Ty13 3) : Ty17 := ⟨Foam.Ty13.d129 x.1, Foam.Ty13.d129 x.2⟩
theorem Ty16.t238 (S : Ty16 G) (g : G) (p : S.Ty24) (hg : g ≠ 1) :
    S.d131 g p ≠ p
      ∧ S.d133 (S.d131 g p) p * S.d133 p (S.d131 g p) = 1
      ∧ Nonempty (S.Ty24 → Unit) := by
  refine ⟨?_, S.t251 p (S.d131 g p), ⟨fun _ => ()⟩⟩
  intro h
  apply hg
  have hs := S.t249 g p
  rw [h, S.t252] at hs
  exact hs.symm

theorem Ty16.t240 (S : Ty16 G) (s t : S.Ty24)
    (h : ∀ p, S.d133 s p = S.d133 t p) : s = t := by
  have h1 := h t
  rw [S.t252] at h1
  have h2 := S.t237 t s
  rw [h1, S.t241] at h2
  exact h2.symm

theorem Ty16.t242 (S : Ty16 G) (p q r : S.Ty24) :
    S.d133 p q * S.d133 q r = S.d133 p r :=
  (S.t250 p q r).symm

def Ty16.d181 (G : Type) [Ty06 G] : Ty16 G where
  Ty24     := G
  d131     := fun g x => g * x
  t241 := fun x => Foam.Ty06.t144 x
  t239 := fun g h x => Foam.Ty06.t141 g h x
  d133     := fun a b => a * Foam.Ty06.d046 b
  t237 := fun p q => by
    show (q * Foam.Ty06.d046 p) * p = q
    rw [Foam.Ty06.t141, Foam.Ty06.t140, Foam.Ty06.t143]
  t249 := fun g p => by
    show (g * p) * Foam.Ty06.d046 p = g
    rw [Foam.Ty06.t141, Foam.Ty06.t142, Foam.Ty06.t143]

theorem Ty16.t243 (S : Ty16 G) (p q r s : S.Ty24) :
    S.d133 p q * S.d133 q r * S.d133 r s * S.d133 s p = 1 := by
  rw [← S.t250 p q r, ← S.t250 p r s]
  exact S.t251 s p

theorem Ty16.t244 (S : Ty16 G) (g : G) (p : S.Ty24) :
    S.d133 p (S.d131 g p)
      * S.d133 (S.d131 g p) (S.d131 g (S.d131 g p))
      * S.d133 (S.d131 g (S.d131 g p)) p = 1 :=
  S.t254 p (S.d131 g p) (S.d131 g (S.d131 g p))

theorem Ty16.t245 (S : Ty16 G) (p : S.Ty24) : S.d132 [] p = p := rfl

theorem Ty16.t246 (S : Ty16 G) (xs ys : List G) (p : S.Ty24) :
    S.d132 (xs ++ ys) p = S.d132 ys (S.d132 xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons g rest ih => exact ih (S.d131 g p)

theorem Ty16.t247 (S : Ty16 G) (p q : S.Ty24) :
    S.d133 p q * S.d133 q p = 1 :=
  S.t251 q p

theorem Ty16.t248 (S : Ty16 G) (p : S.Ty24) : S.d133 p p = 1 :=
  S.t252 p

theorem Ty16.t250 (S : Ty16 G) (p q r : S.Ty24) :
    S.d133 p r = S.d133 p q * S.d133 q r := by
  have e : S.d131 (S.d133 p q * S.d133 q r) r = p := by
    rw [S.t239, S.t237 r q, S.t237 q p]
  have h := S.t249 (S.d133 p q * S.d133 q r) r
  rw [e] at h
  exact h

theorem Ty16.t251 (S : Ty16 G) (p q : S.Ty24) : S.d133 q p * S.d133 p q = 1 := by
  have e : S.d131 (S.d133 q p * S.d133 p q) q = q := by
    rw [S.t239, S.t237 q p, S.t237 p q]
  have h := S.t249 (S.d133 q p * S.d133 p q) q
  rw [e, S.t252] at h
  exact h.symm

theorem Ty16.t252 (S : Ty16 G) (p : S.Ty24) : S.d133 p p = 1 := by
  have h := S.t249 1 p
  rw [S.t241] at h
  exact h

def Ty16.d182 (S : Ty16 G) : Ty18 where
  Ty27 := S.Ty24
  Ty26 := S.Ty24
  Ty25   := G
  d134   := S.d133

theorem Ty16.t253 (S : Ty16 G) (p q r : S.Ty24) :
    S.d132 [S.d133 q p, S.d133 r q, S.d133 p r] p = p := by
  show S.d131 (S.d133 p r) (S.d131 (S.d133 r q) (S.d131 (S.d133 q p) p)) = p
  rw [S.t237 p q, S.t237 q r, S.t237 r p]

theorem Ty16.t254 (S : Ty16 G) (p q r : S.Ty24) :
    S.d133 p q * S.d133 q r * S.d133 r p = 1 := by
  rw [← S.t250 p q r]
  exact S.t251 r p

def Ty18.d183 (S : Ty18) : Ty01 S.Ty27 := ⟨S.Ty26, S.Ty25, S.d134⟩

def Ty18.d184 (S T : Ty18) : Ty18 where
  Ty27 := S.Ty27 × T.Ty27
  Ty26 := S.Ty26 × T.Ty26
  Ty25   := S.Ty25 × T.Ty25
  d134   := fun st pq => (S.d134 st.1 pq.1, T.d134 st.2 pq.2)

def Ty28.d185 {S T U : Ty18} (g : Ty28 T U) (f : Ty28 S T) : Ty28 S U where
  d139  := fun s => g.d139 (f.d139 s)
  d138  := fun p => g.d138 (f.d138 p)
  d137    := fun a => g.d137 (f.d137 a)
  t255 := fun s p => by
    show U.d134 (g.d139 (f.d139 s)) (g.d138 (f.d138 p))
       = g.d137 (f.d137 (S.d134 s p))
    rw [g.t255 (f.d139 s) (f.d138 p), f.t255 s p]

theorem t256 (κ a : Int) : d140 κ ⟨a, 0⟩ ⟨1, 0⟩ = a := by
  show a * 1 - κ * (0 * 0) = a
  rw [t020, t022, t022, t052]

theorem t257 (z : Ty05) : Foam.Ty05.d109 Foam.Ty05.d042.d115 z = z.d041 := by
  show (0 : Int) * z.d043 + 1 * z.d041 = z.d041
  rw [Foam.t055, Foam.t037, Foam.t054]

theorem t258 (z : Ty05) : Foam.Ty05.d109 Foam.Ty05.d042 z = z.d043 := by
  show 1 * z.d043 + 0 * z.d041 = z.d043
  rw [Foam.t037, Foam.t055, Foam.t004 z.d043 0, Foam.t054]

theorem t259 [DecidableEq S] (l : List S) (s : S) :
    Foam.Ty05.d109 Foam.Ty05.d042 (d089 id l s) = Int.ofNat (Foam.Ty08.d003 l s) := by
  rw [t168, t258]

theorem t260 : t137 Foam.Ty05.d113 2 := fun z => Foam.Ty05.t210 z

theorem t261 [DecidableEq S] (l : List (Option S)) (s : S) :
    d090 Foam.Ty05.d115 (none :: none :: none :: none :: l) s = d090 Foam.Ty05.d115 l s := by
  show ((((d090 Foam.Ty05.d115 l s).d115).d115).d115).d115 = d090 Foam.Ty05.d115 l s
  exact Foam.Ty05.t214 _

theorem t264 (n : Nat) (a c : Int) (p : Unit) :
    d085.d102 (n, a) p = d085.d102 (n, c) p := rfl

theorem t265 (n : Nat) (_ : t137 Foam.Ty05.d113 n) :
    t137 (fun w => w) n := t273 n

theorem t266 (n : Nat) (h : t137 Foam.Ty05.d115 n) : t137 Foam.Ty05.d113 n := by
  intro z
  have e : d096 n Foam.Ty05.d113 z = d096 n Foam.Ty05.d115 (d096 n Foam.Ty05.d115 z) := by
    rw [t175 Foam.Ty05.d113 (fun w => Foam.Ty05.d115 (Foam.Ty05.d115 w))
          (fun w => (Foam.Ty05.t216 w).symm) n z]
    exact t174 Foam.Ty05.d115 n z
  rw [e, h (d096 n Foam.Ty05.d115 z), h z]

def d186 : Ty02 Ty21 := d093 d144

def d187 {State R : Type} (a b : Ty01 State)
    (g : a.Ty19 → b.Ty19 → R) (s : State) (p : a.Ty20) (q : b.Ty20) : R :=
  g (a.d102 s p) (b.d102 s q)

theorem t267 (w z : Ty05) :
    Foam.Ty05.d112 w.d110 z = ⟨Foam.Ty05.d109 w z, Foam.Ty05.d111 w z⟩ := by
  show (⟨w.d043 * z.d043 - -w.d041 * z.d041, w.d043 * z.d041 + -w.d041 * z.d043⟩ : Ty05)
    = ⟨w.d043 * z.d043 + w.d041 * z.d041, w.d043 * z.d041 - w.d041 * z.d043⟩
  rw [t027 w.d041 z.d041, t027 w.d041 z.d043,
    Int.sub_eq_add_neg (a := w.d043 * z.d043) (b := -(w.d041 * z.d041)),
    Int.neg_neg, ← Int.sub_eq_add_neg]

theorem t268 (a b : Ty05) : (a.d108 b).d110 = a.d110.d108 b.d110 := by
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      show (⟨a1 + b1, -(a2 + b2)⟩ : Ty05) = ⟨a1 + b1, -a2 + -b2⟩
      rw [Foam.t025]

theorem t269 (c : Prop) [inst : Decidable c] :
    (if c then Foam.Ty05.d042 else Foam.Ty05.d044).d110 = (if c then Foam.Ty05.d042 else Foam.Ty05.d044) := by
  cases inst with
  | isTrue _ => rfl
  | isFalse _ => rfl

theorem t270 (z : Ty05) : (z.d115).d110 = d098 3 z.d110 := by
  cases z with
  | mk a b =>
    show (⟨-b, -a⟩ : Ty05) = ⟨- - -b, -a⟩
    rw [Int.neg_neg]

theorem t273 (n : Nat) : t137 (fun w => w) n := t176 n

theorem t274 (a : Int) : d142 ⟨a, 0⟩ ⟨1, 0⟩ = 0 := by
  show a * 0 - 0 * 1 = 0
  rw [t022, t055, t052]

theorem t275 (θ z : Ty05) :
    Foam.Ty05.d109 θ.d115 z = Foam.Ty05.d111 θ z := by
  show -θ.d041 * z.d043 + θ.d043 * z.d041 = θ.d043 * z.d041 - θ.d041 * z.d043
  rw [t027 θ.d041 z.d043,
    Int.sub_eq_add_neg (a := θ.d043 * z.d041) (b := θ.d041 * z.d043),
    t004 (-(θ.d041 * z.d043)) (θ.d043 * z.d041)]

theorem t276 (w z : Ty05) :
    Foam.Ty05.d111 w.d115 z.d115 = Foam.Ty05.d111 w z := by
  show -w.d041 * z.d043 - w.d043 * -z.d041 = w.d043 * z.d041 - w.d041 * z.d043
  rw [t027 w.d041 z.d043, t018 w.d043 z.d041,
    Int.sub_eq_add_neg (a := -(w.d041 * z.d043)) (b := -(w.d043 * z.d041)),
    Int.neg_neg,
    Int.sub_eq_add_neg (a := w.d043 * z.d041) (b := w.d041 * z.d043),
    t004 (-(w.d041 * z.d043)) (w.d043 * z.d041)]

theorem t277 (θ z : Ty05) :
    Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z)
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z))
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = 0 :=
  Foam.Ty05.t208 θ z

def d188 : Ty09 := ⟨Foam.Ty10.d123, Foam.Ty10.d060⟩

theorem t279 : t137 Foam.Ty05.d115 4 := t322

def d189 (d₀ : D) (x : List B) : List (List B) :=
  d150 (d013 knows learn) d012 (d₀, []) x

def d190 {State : Type} (s : State × Ty05) : State × Ty05 := (s.1, Foam.Ty05.d115 s.2)

theorem t280 (z : Ty05) : (Foam.Ty05.d115 z).d114 = z.d114 := by
  show (-z.d041) * (-z.d041) + z.d043 * z.d043 = z.d043 * z.d043 + z.d041 * z.d041
  rw [Foam.t027, Foam.t018, Int.neg_neg, Foam.t004]

theorem t281 (S : Ty18) (f : Ty28 S d101) : f = d143 S := rfl

def d191 : Ty09 := ⟨d092, Foam.Ty10.d123⟩
theorem t282 : d145 ≠ d144 := fun h => absurd (congrArg Prod.snd h) (by decide)

theorem t283 (f : Int → Int)
    (h : ∀ θ z : Ty05,
      f (Foam.Ty05.d109 θ z) + f (Foam.Ty05.d111 θ z) = θ.d114 * z.d114) :
    ∀ a : Int, f a = a * a := by
  have h0 : f 0 = 0 := t078 (f 0) (h Foam.Ty05.d044 Foam.Ty05.d044)
  intro a
  have ha : f (a * 1 + 0 * 0) + f (a * 0 - 0 * 1)
      = (a * a + 0 * 0) * (1 * 1 + 0 * 0) := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [t014 a 1, Int.one_mul a, t014 a 0, t055 a,
    show (0 : Int) * 0 = 0 from rfl, show (0 : Int) * 1 = 0 from rfl,
    show (1 : Int) * 1 = 1 from rfl, show (0 : Int) - 0 = 0 from rfl,
    Int.add_zero a, Int.add_zero (a * a),
    show (1 : Int) + 0 = 1 from rfl,
    t014 (a * a) 1, Int.one_mul (a * a), h0, Int.add_zero (f a)] at ha
  exact ha

theorem t284 (κ : Int) (f : Int → Int)
    (h : ∀ w z : Ty05, f (d140 κ w z) - κ * f (d142 w z) = d149 κ w * d149 κ z) :
    ∀ a : Int, f a = a * a + κ * f 0 := by
  intro a
  have ha := h ⟨a, 0⟩ ⟨1, 0⟩
  rw [t256 κ a, t274 a, t303 κ a, t304 κ,
      t014 (a * a) 1, t037] at ha
  rw [← t048 (a := f a) (b := κ * f 0), ha]

theorem t285 {S : Type} (s : S) (l : List S) :
    ∃ n, (d152 l).d033 n ≠ (d093 s).d033 n :=
  ⟨l.length, fun h => nomatch (t125 l).symm.trans h⟩

theorem t287 :
    d141 (Int.negSucc 0) (Int.negSucc 0) = 0 := rfl

theorem t288 (k : Nat) :
    d141 (Int.negSucc (k + 1)) (Int.negSucc (k + 1)) = Int.negSucc k := rfl

theorem t289 (v : Int) (z : Ty03) :
    (d146 v z).d104 = z.d104 := rfl

theorem t290 (v1 v2 : Int) (z : Ty03) :
    d146 v2 (d146 v1 z) = d146 (v2 + v1) z := by
  show (⟨z.d036, v2 * z.d036 + (v1 * z.d036 + z.d037)⟩ : Ty03) = ⟨z.d036, (v2 + v1) * z.d036 + z.d037⟩
  rw [t007 v2 v1 z.d036, t005 (v2 * z.d036) (v1 * z.d036) z.d037]

theorem t298 (a b : Int) (h : Foam.Ty14.d130 ⟨a, b⟩ = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) :=
  t081 a b h

theorem t299 (w z : Ty14) :
    d147 w z * d147 w z - d148 w z * d148 w z = Foam.Ty14.d130 w * Foam.Ty14.d130 z := by
  show (w.d076 * z.d076 - w.d077 * z.d077) * (w.d076 * z.d076 - w.d077 * z.d077)
        - (w.d076 * z.d077 - w.d077 * z.d076) * (w.d076 * z.d077 - w.d077 * z.d076)
      = (w.d076 * w.d076 - w.d077 * w.d077) * (z.d076 * z.d076 - z.d077 * z.d077)
  exact t079 w.d076 w.d077 z.d076 z.d077

theorem t300 :
    d147 ⟨2, 1⟩ ⟨3, 1⟩ * d147 ⟨2, 1⟩ ⟨3, 1⟩
        - d148 ⟨2, 1⟩ ⟨3, 1⟩ * d148 ⟨2, 1⟩ ⟨3, 1⟩
      = Foam.Ty14.d130 ⟨2, 1⟩ * Foam.Ty14.d130 ⟨3, 1⟩ := by decide

theorem t301 (x : Ty13 0) : Foam.Ty13.d127 0 x ≠ Foam.Ty10.d122 d097 :=
  fun h => t178 (congrArg Prod.snd h).symm

theorem t302 (z w : Ty05) :
    Foam.Ty05.d109 z w * Foam.Ty05.d109 z w + Foam.Ty05.d111 z w * Foam.Ty05.d111 z w
      = z.d114 * w.d114 := by
  show Foam.Ty05.d109 z w * Foam.Ty05.d109 z w + Foam.Ty05.d111 z w * Foam.Ty05.d111 z w
    = (z.d043 * z.d043 + z.d041 * z.d041) * (w.d043 * w.d043 + w.d041 * w.d041)
  rw [show Foam.Ty05.d111 z w = -(z.d041 * w.d043) + z.d043 * w.d041 by
    show z.d043 * w.d041 - z.d041 * w.d043 = -(z.d041 * w.d043) + z.d043 * w.d041
    rw [Int.sub_eq_add_neg (a := z.d043 * w.d041) (b := z.d041 * w.d043),
      t004 (z.d043 * w.d041) (-(z.d041 * w.d043))]]
  exact Foam.t059 z.d043 z.d041 w.d043 w.d041

def d192 : Ty09 := ⟨d097, Foam.Ty10.d123⟩
theorem t303 (κ a : Int) : d149 κ ⟨a, 0⟩ = a * a := by
  show a * a - κ * (0 * 0) = a * a
  rw [t022, t022, t052]

theorem t304 (κ : Int) : d149 κ ⟨1, 0⟩ = 1 := by
  show 1 * 1 - κ * (0 * 0) = 1
  rw [t037, t022, t022, t052]

theorem t305 : ∃ z : Ty05, d149 (-1) z ≠ d149 1 z := ⟨⟨1, 1⟩, by decide⟩

theorem t306 (z : Ty05) : z.d114 = Foam.Ty05.d109 z z := rfl

theorem t307 {S B O : Type} (step : S → B → S × List O) (flush : S → List O)
    (init : S) (xs ys : List B) :
    d150 step flush init (xs ++ ys)
      = d026 step init xs ++ d150 step flush (d099 step init xs) ys := by
  show d026 step init (xs ++ ys) ++ flush (d099 step init (xs ++ ys))
     = d026 step init xs ++ (d026 step (d099 step init xs) ys
        ++ flush (d099 step (d099 step init xs) ys))
  rw [t188, t189, t070]

theorem t308 (v1 v2 : Int) (z : Ty03) :
    d146 v2 (d146 v1 z) = d146 (v2 + v1) z :=
  t290 v1 v2 z

theorem t309 (v : Int) (hv : v ≠ 0) :
    d146 v ⟨1, 0⟩ ≠ (⟨1, 0⟩ : Ty03) := by
  intro h
  have hx : v * 1 + 0 = 0 := congrArg Foam.Ty03.d037 h
  rw [Foam.t020, Int.add_zero] at hx
  exact hv hx

theorem t310 :
    t073 (d141 (-1) (d141 (-1) (-1))) := ⟨1, rfl⟩

def d193 {S : Type} (s : S) : Ty15 (List S) (Ty02 S) where
  d079       := d152
  t158 := fun {l l'} h => t311 l l' (fun n => congrArg (fun c => c.d033 n) h)
  t157  := ⟨d093 s, fun l h => (t285 s l).elim (fun n hn => hn (congrArg (fun c => c.d033 n) h))⟩

theorem t311 {S : Type} (l l' : List S)
    (h : ∀ n, (d152 l).d033 n = (d152 l').d033 n) : l = l' :=
  t124 l l' h

theorem t312 {S : Type} (s : S) :
    ¬ ∃ g : Ty02 S → List S, ∀ c, d152 (g c) = c :=
  Foam.Ty15.t159 (d193 s)

def d194 : Ty01 Ty04 where
  Ty20 := Bool
  Ty19   := Ty21
  d102   := fun f p => bif p then f.d106 else f.d105

theorem t314 :
    ∃ s t : Nat × Int, (∀ p : Unit, d085.d102 s p = d085.d102 t p) ∧ s ≠ t :=
  ⟨(0, d014 1 * d014 1 - d014 2 * d014 0),
   (0, 0),
   fun _ => rfl,
   fun h => by
     have hc := t112 0
     have : d014 1 * d014 1 - d014 2 * d014 0 = (0 : Int) := congrArg Prod.snd h
     rw [this] at hc
     exact absurd hc (by decide)⟩

theorem t315 :
    d090 Foam.Ty05.d115 [some true] true ≠ d090 Foam.Ty05.d115 [none, some true] true := by
  decide

theorem t316 (n : Nat) (a b : Ty05) :
    d098 n (a.d108 b) = (d098 n a).d108 (d098 n b) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show Foam.Ty05.d115 (d098 m (a.d108 b)) = (Foam.Ty05.d115 (d098 m a)).d108 (Foam.Ty05.d115 (d098 m b))
    rw [ih, t318]

theorem t318 (a b : Ty05) : (a.d108 b).d115 = a.d115.d108 b.d115 := by
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      show (⟨-(a2 + b2), a1 + b1⟩ : Ty05) = ⟨-a2 + -b2, a1 + b1⟩
      rw [Foam.t025]

theorem t319 {S : Type} (s : S) :
    (∀ l l' : List S, (∀ n, (d152 l).d033 n = (d152 l').d033 n) → l = l')
      ∧ ¬ ∃ g : Ty02 S → List S, ∀ c, d152 (g c) = c :=
  ⟨t311, t312 s⟩

def d195 : Ty17 := ⟨⟨Foam.Ty10.d123, d092⟩, ⟨Foam.Ty10.d123, d097⟩⟩

theorem t320 : ∀ b : Int, d022 (d141 b b) = d022 b
  | Int.ofNat _ => rfl
  | Int.negSucc 0 => rfl
  | Int.negSucc (_ + 1) => rfl

theorem t321 (m : Nat) :
    d141 (Int.ofNat m) (Int.ofNat m) = Int.ofNat m := rfl

def d196 (S : Ty18) (p : S.Ty26) : Ty18 where
  Ty27 := S.Ty27
  Ty26 := Unit
  Ty25   := S.Ty25
  d134   := fun s _ => S.d134 s p

def d197 [DecidableEq S] : List S → S → Ty05 := d089 Foam.Ty05.d115

theorem t322 : t137 Foam.Ty05.d115 4 := fun z => Foam.Ty05.t214 z

theorem t323 {S : Type} [DecidableEq S] (new old : List S) (s : S) :
    d089 Foam.Ty05.d115 (new ++ old) s = d091 Foam.Ty05.d115 new s (d089 Foam.Ty05.d115 old s) :=
  t197 Foam.Ty05.d115 new old s

theorem t324 :
    d141 (-1) (d141 (-1) (-1)) = 1 := rfl

theorem t327 (S : Ty18) (ps : List S.Ty26) :
    ∀ {t s : S.Ty27}, (∀ p, S.d134 t p = S.d134 s p) →
      d153 S t ps = d153 S s ps := by
  induction ps with
  | nil => intro t s _; rfl
  | cons p ps ih =>
    intro t s h
    show S.d134 t p :: d153 S t ps = S.d134 s p :: d153 S s ps
    rw [h p, ih h]

def d198 (x : Ty21) (f : Ty04) : Ty04 := { f with d105 := x }
def d199 (y : Ty21) (f : Ty04) : Ty04 := { f with d106 := y }

theorem t331 (κ : Int) (f : Int → Int)
    (h : ∀ w z : Ty05, f (d140 κ w z) - κ * f (d142 w z) = d149 κ w * d149 κ z) :
    (1 - κ) * f 0 = 0 := by
  have hf0 := t284 κ f h 0
  rw [t055, t054] at hf0
  show (1 - κ) * f 0 = 0
  rw [Int.sub_eq_add_neg (a := 1) (b := κ), t007 1 (-κ) (f 0), t037,
      t027 κ (f 0), ← hf0, t008]

theorem Ty01.t332 (a : Ty01 State) : a.t198 a :=
  ⟨id, id, fun _ _ => rfl⟩

theorem Ty01.t333 {a b c : Ty01 State}
    (hab : a.t198 b) (hbc : b.t198 c) : a.t198 c := by
  obtain ⟨e1, g1, h1⟩ := hab
  obtain ⟨e2, g2, h2⟩ := hbc
  refine ⟨fun p => e1 (e2 p), fun x => g2 (g1 x), fun s p => ?_⟩
  rw [h2 s p, h1 s (e2 p)]

def Ty01.d200 (b : Ty01 State) (n : Nat) : Ty01 State where
  Ty20 := (b.d156 n).Ty20
  Ty19 := (b.d156 n).Ty19
  d102 := fun s p => (b.d156 n).d102 (s, Foam.Ty08.d052 n) p

theorem Ty01.t334 {State : Type} (b : Ty01 State) :
    b.d161.d183 = b := rfl

theorem t335 : Foam.d164 Foam.d031 Foam.d162 = Foam.Ty05.d044 := by decide
theorem t336 : Foam.d164 Foam.d031 Foam.d103 = Foam.Ty05.d044 := by decide
theorem t337 : Foam.d164 Foam.d031 Foam.d031 = ⟨4, 0⟩ := by decide
theorem t338 (a b : Ty12) :
    Foam.d162 (a * b) = Foam.Ty05.d112 (Foam.d162 a) (Foam.d162 b) := by
  cases a <;> cases b <;> decide

theorem t339 : Foam.d164 Foam.d162 Foam.d162 = ⟨4, 0⟩ := by decide

theorem t340 (a : Ty12) : (Foam.d162 a).d114 = 1 := by
  cases a <;> decide

theorem t341 : Foam.d164 Foam.d103 Foam.d162 = Foam.Ty05.d044 := by decide

theorem t342 : Foam.d103 ≠ Foam.d162 := by
  intro h
  have : Foam.d103 Foam.Ty12.c2 = Foam.d162 Foam.Ty12.c2 := by rw [h]
  exact absurd this (by decide)

theorem t343 : Foam.d164 Foam.d103 Foam.d103 = ⟨4, 0⟩ := by decide
theorem t344 : Foam.d164 Foam.d032 Foam.d031 = Foam.Ty05.d044 := by decide
theorem t345 : Foam.d164 Foam.d032 Foam.d162 = Foam.Ty05.d044 := by decide
theorem t346 : Foam.d164 Foam.d032 Foam.d103 = Foam.Ty05.d044 := by decide
theorem t347 : Foam.d164 Foam.d032 Foam.d032 = ⟨4, 0⟩ := by decide
theorem t348 (n0 n1 n2 n3 : Int) (f : Ty12 → Ty05) :
    (Foam.d163 n0 n1 n2 n3 f).d041
      = (n0 * (f Foam.Ty12.c1).d041 + n1 * (f Foam.Ty12.c2).d041) + (n2 * (f Foam.Ty12.c3).d041 + n3 * (f Foam.Ty12.c4).d041) := by
  show ((Foam.Ty05.d112 ⟨n0,0⟩ (f Foam.Ty12.c1)).d041 + (Foam.Ty05.d112 ⟨n1,0⟩ (f Foam.Ty12.c2)).d041
       + ((Foam.Ty05.d112 ⟨n2,0⟩ (f Foam.Ty12.c3)).d041 + (Foam.Ty05.d112 ⟨n3,0⟩ (f Foam.Ty12.c4)).d041))
     = (n0 * (f Foam.Ty12.c1).d041 + n1 * (f Foam.Ty12.c2).d041) + (n2 * (f Foam.Ty12.c3).d041 + n3 * (f Foam.Ty12.c4).d041)
  rw [Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209]

theorem t349 (n0 n1 n2 n3 : Int) (f : Ty12 → Ty05) :
    (Foam.d163 n0 n1 n2 n3 f).d043
      = (n0 * (f Foam.Ty12.c1).d043 + n1 * (f Foam.Ty12.c2).d043) + (n2 * (f Foam.Ty12.c3).d043 + n3 * (f Foam.Ty12.c4).d043) := by
  show ((Foam.Ty05.d112 ⟨n0,0⟩ (f Foam.Ty12.c1)).d043 + (Foam.Ty05.d112 ⟨n1,0⟩ (f Foam.Ty12.c2)).d043
       + ((Foam.Ty05.d112 ⟨n2,0⟩ (f Foam.Ty12.c3)).d043 + (Foam.Ty05.d112 ⟨n3,0⟩ (f Foam.Ty12.c4)).d043))
     = (n0 * (f Foam.Ty12.c1).d043 + n1 * (f Foam.Ty12.c2).d043) + (n2 * (f Foam.Ty12.c3).d043 + n3 * (f Foam.Ty12.c4).d043)
  rw [Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209, Foam.Ty05.t209]

def d201 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d031).d043
def d202 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d032).d043
def d203 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d103).d041

def d204 (n0 n1 n2 n3 : Int) : Int := (Foam.d163 n0 n1 n2 n3 Foam.d103).d043
def Ty22.d205 {S T : Ty18} (F : Ty22 S) (G : Ty22 T) :
    Ty22 (Foam.Ty18.d184 S T) where
  t139      := fun st st' => F.t139 st.1 st'.1 ∧ G.t139 st.2 st'.2
  t350 := fun st st' h pq => by
    show (S.d134 st.1 pq.1, T.d134 st.2 pq.2) = (S.d134 st'.1 pq.1, T.d134 st'.2 pq.2)
    rw [F.t350 st.1 st'.1 h.1 pq.1, G.t350 st.2 st'.2 h.2 pq.2]

theorem Ty05.t351 (w z : Ty05) : ∃ k : Nat, Foam.Ty05.d165 w z = Int.ofNat k :=
  Foam.Ty05.t056 (Foam.Ty05.d109 w z)

theorem Ty05.t352 (θ z : Ty05) :
    Foam.Ty05.d165 θ z + Foam.Ty05.d165 (Foam.Ty05.d115 θ) z = Foam.Ty05.d114 θ * Foam.Ty05.d114 z := by
  show (θ.d043 * z.d043 + θ.d041 * z.d041) * (θ.d043 * z.d043 + θ.d041 * z.d041)
     + ((-θ.d041) * z.d043 + θ.d043 * z.d041) * ((-θ.d041) * z.d043 + θ.d043 * z.d041)
     = (θ.d043 * θ.d043 + θ.d041 * θ.d041) * (z.d043 * z.d043 + z.d041 * z.d041)
  rw [t027 θ.d041 z.d043]
  exact Foam.t059 θ.d043 θ.d041 z.d043 z.d041

theorem Ty05.t353 (θ a b : Ty05) :
    Foam.Ty05.d165 θ (Foam.Ty05.d108 a b)
      = Foam.Ty05.d165 θ a + Foam.Ty05.d165 θ b + 2 * (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b) := by
  show Foam.Ty05.d109 θ (Foam.Ty05.d108 a b) * Foam.Ty05.d109 θ (Foam.Ty05.d108 a b)
     = Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ a + Foam.Ty05.d109 θ b * Foam.Ty05.d109 θ b
       + 2 * (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b)
  rw [Foam.Ty05.t206 θ a b, Foam.t065 (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b),
      t007 (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ a + Foam.Ty05.d109 θ b),
      t015 (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ b),
      t015 (Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ b),
      t014 (Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ a)]
  exact Foam.t057 (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ a) (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b)
        (Foam.Ty05.d109 θ a * Foam.Ty05.d109 θ b) (Foam.Ty05.d109 θ b * Foam.Ty05.d109 θ b)

def t354 (bank : List (Ty01 State)) (q : Ty01 State) : Prop :=
  ∃ p ∈ bank, p.t198 q

def d206 (S C : Type) [DecidableEq S] : Ty18 :=
  ⟨List S × C, S, Nat × Ty05, fun st s => (Foam.Ty08.d003 st.1 s, d197 st.1 s)⟩

def Ty09.d207 (X Y : Ty09) : Ty09 := ⟨Foam.Ty10.d170 X.d053 Y.d053, Foam.Ty10.d170 X.d054 Y.d054⟩
def Ty09.d208 (X : Ty09) : Ty09 := ⟨Foam.Ty10.d171 X.d053, Foam.Ty10.d121 X.d054⟩
def Ty09.d209 (X Y : Ty09) : Ty09 :=
  ⟨Foam.Ty10.d173 (Foam.Ty10.d172 X.d053 Y.d053) (Foam.Ty10.d172 (Foam.Ty10.d171 Y.d054) X.d054),
   Foam.Ty10.d170 (Foam.Ty10.d172 Y.d054 X.d053) (Foam.Ty10.d172 X.d054 (Foam.Ty10.d171 Y.d053))⟩

def Ty09.d210 (X Y : Ty09) : Ty09 := ⟨Foam.Ty10.d173 X.d053 Y.d053, Foam.Ty10.d173 X.d054 Y.d054⟩

theorem Ty09.t355 (x : Ty13 2) : Foam.Ty09.d167 (Foam.Ty13.d129 x) = x := rfl

def t356 (bank : List (Ty01 State)) : Prop :=
  ∀ a ∈ bank, ∀ b ∈ bank, a.t198 b → b.t198 a

def t359 (write : Ty21 → Ty04 → Ty04) (p : Bool) : Prop :=
  ∃ dec : Ty21 → Ty21, ∀ x f, dec (d194.d102 (write x f) p) = x

def Ty12.d213 : Ty12 → Ty10
  | Foam.Ty12.c1 => Foam.Ty10.d060
  | Foam.Ty12.c2 => d092
  | Foam.Ty12.c3 => Foam.Ty10.d059
  | Foam.Ty12.c4 => Foam.Ty10.d172 Foam.Ty10.d059 d092

theorem Ty13.t360 (o : Ty09) : Foam.Ty13.d129 (Foam.Ty09.d167 o) = o := rfl
theorem Ty13.t361 (x y : Ty13 1) :
    Foam.Ty13.d073 (Foam.Ty13.d069 1 x y) = Foam.Ty10.d172 (Foam.Ty13.d073 x) (Foam.Ty13.d073 y) := rfl

def Ty16.d214 (S : Ty16 G) (origin : S.Ty24) : Ty07 S.Ty24 G where
  d051     := fun p => S.d133 p origin
  d049     := fun g => S.d131 g origin
  t146 := fun g => S.t249 g origin
  t145 := fun p => S.t237 origin p

def Ty17.d215 (s : Ty17) : Ty13 3 := (Foam.Ty09.d167 s.d081, Foam.Ty09.d167 s.d082)

def Ty17.d216 : Ty17 := ⟨Foam.Ty09.d168, Foam.Ty09.d168⟩

theorem Ty18.t362 (S : Ty18) : S.d183.d161 = S := rfl

theorem Ty28.t363 {S T U V : Ty18}
    (h : Ty28 U V) (g : Ty28 T U) (f : Ty28 S T) :
    (h.d185 g).d185 f = h.d185 (g.d185 f) := rfl

theorem Ty28.t364 {S T : Ty18} (f : Ty28 S T) :
    f.d185 (Foam.Ty28.d136 S) = f := rfl

def Ty28.d217 (S T : Ty18) : Ty28 (Foam.Ty18.d184 S T) S where
  d139  := fun st => st.1
  d138  := fun pq => pq.1
  d137    := fun a => a.1
  t255 := fun _ _ => rfl

theorem Ty28.t365 {S T : Ty18} (f : Ty28 S T) :
    (Foam.Ty28.d136 T).d185 f = f := rfl

def Ty28.d218 {X S T : Ty18} (f : Ty28 X S) (g : Ty28 X T) :
    Ty28 X (Foam.Ty18.d184 S T) where
  d139  := fun x => (f.d139 x, g.d139 x)
  d138  := fun p => (f.d138 p, g.d138 p)
  d137    := fun a => (f.d137 a, g.d137 a)
  t255 := fun x p => by
    show (S.d134 (f.d139 x) (f.d138 p), T.d134 (g.d139 x) (g.d138 p))
       = (f.d137 (X.d134 x p), g.d137 (X.d134 x p))
    rw [f.t255 x p, g.t255 x p]

def Ty28.d219 (S T : Ty18) : Ty28 (Foam.Ty18.d184 S T) T where
  d139  := fun st => st.2
  d138  := fun pq => pq.2
  d137    := fun a => a.2
  t255 := fun _ _ => rfl

def d220 : Ty15 (List Ty21) (Ty02 Ty21) := d193 d144

def d221 (f : Ty04) : Ty04 := d199 (d194.d102 f d023) f

theorem t366 (θ z : Ty05) :
    Foam.Ty05.d165 θ z + Foam.Ty05.d165 (Foam.Ty05.d115 θ) z = Foam.Ty05.d114 θ * Foam.Ty05.d114 z :=
  Foam.Ty05.t352 θ z

theorem t367 (θ z : Ty05) :
    Foam.Ty05.d165 θ z + Foam.Ty05.d165 θ.d115 z
      = Foam.Ty05.d109 θ z * Foam.Ty05.d109 θ z + Foam.Ty05.d111 θ z * Foam.Ty05.d111 θ z := by
  show Foam.Ty05.d109 θ z * Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ.d115 z * Foam.Ty05.d109 θ.d115 z
    = Foam.Ty05.d109 θ z * Foam.Ty05.d109 θ z + Foam.Ty05.d111 θ z * Foam.Ty05.d111 θ z
  rw [t275 θ z]

def d222 : Ty16 Ty12 := Foam.Ty16.d181 Ty12

theorem t369 {State R : Type} (a b : Ty01 State)
    (g : a.Ty19 → b.Ty19 → R) (s : State) (p : a.Ty20) (q : b.Ty20) :
    d187 a b g s p q = g ((a.d159 b).d102 s (p, q)).1 ((a.d159 b).d102 s (p, q)).2 :=
  rfl

theorem t370 (b : Ty01 State) (n : Nat)
    (s : State) (l m : Ty08 n) (p : b.Ty20) :
    (b.d156 n).d102 (s, l) p = (b.d156 n).d102 (s, m) p := rfl

theorem t371 (b : Ty01 State) (n : Nat)
    (s : State × Ty08 n) (p : b.Ty20) :
    (b.d156 n).d102 s p = b.d102 s.1 p := rfl

theorem t372 (b : Ty01 State) :
    b.d155.d157.t198 b.d155.d157 ∧
      b.d155.d157.t198 b ∧ b.t198 b.d155.d157 :=
  ⟨Foam.Ty01.t332 _, t374 b⟩

theorem t373 (b : Ty01 State)
    (s : State) (n m : Int) (p : b.Ty20) :
    b.d155.d102 (s, n) p = b.d155.d102 (s, m) p := rfl

theorem t374 (b : Ty01 State) :
    b.d155.d157.t198 b ∧ b.t198 b.d155.d157 :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

def d223 (S : Ty18) (p : S.Ty26) : Ty28 (d196 S p) S where
  d139  := fun s => s
  d138  := fun _ => p
  d137    := fun a => a
  t255 := fun _ _ => rfl

theorem t375 (S : Ty18) (p : S.Ty26) (s : S.Ty27) :
    (d196 S p).d134 s () = S.d134 s p := rfl

theorem t376 {State : Type} (s : State × Ty05) :
    d190 (d190 (d190 (d190 s))) = s := by
  show (s.1, Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 s.2)))) = s
  rw [Foam.Ty05.t214]

theorem t377 {State : Type} (s : State × Ty05) :
    (d190 s).2.d114 = s.2.d114 :=
  t280 s.2

theorem t378 {State : Type} (b : Ty01 State) (s : State × Ty05) (p : b.Ty20) :
    b.d160.d102 (d190 s) p = b.d160.d102 s p := rfl

theorem t379 : Foam.Ty10.d172 d092 d092 = Foam.Ty10.d059 := by decide
theorem t380 (f : Ty04) (a b : Int) :
    ¬ ∃ p, d194.d155.d102 (f, a) p ≠ d194.d155.d102 (f, b) p :=
  fun ⟨_, hp⟩ => hp rfl

theorem t381 :
    t205 (d198 d145) d194 ∧ t205 (d199 d145) d194 :=
  ⟨⟨⟨d144, d144⟩, d023, fun h => t282 h⟩,
   ⟨⟨d144, d144⟩, d024, fun h => t282 h⟩⟩

theorem t382 (S : Ty18) (m n : S.Ty27 → S.Ty27)
    (hm : t217 S m) (hn : t217 S n) : t217 S (fun s => m (n s)) :=
  fun s p => (hm (n s) p).trans (hn s p)

theorem t383 (S : Ty18) : t217 S (fun s => s) := fun _ _ => rfl

theorem t384 : Foam.Ty10.d172 d097 d097 = Foam.Ty10.d059 := by decide
def d224 : Ty10 := Foam.Ty10.d172 d092 d097

theorem t385 (d₀ : D) (x : List B) :
    d088 (d189 knows learn d₀ x) = x := by
  show d017 (d026 (d013 knows learn) (d₀, []) x
        ++ d012 (d099 (d013 knows learn) (d₀, []) x)) = x
  rw [t115, t116]
  exact (t166 knows learn (d₀, []) x).trans rfl

theorem t386 (S : Ty18) (m : S.Ty27 → S.Ty27)
    (h : t217 S m) (ps : List S.Ty26) :
    ∀ s, d154 S m s ps = d153 S s ps := by
  induction ps with
  | nil => intro s; rfl
  | cons p ps ih =>
    intro s
    show S.d134 (m s) p :: d154 S m (m s) ps = S.d134 s p :: d153 S s ps
    rw [h s p, ih (m s), t327 S ps (h s)]

theorem t387 :
    ∃ (s t : Nat × Int) (p : (d085.d158 0).Ty20),
      t076 d085.d102 s t ∧
        (d085.d158 0).d102 s p ≠ (d085.d158 0).d102 t p :=
  ⟨(0, 0), (0, 1), none, fun _ => rfl, by
    intro h
    exact absurd (Sum.inr.inj h) (by decide)⟩

theorem t388 (b : Ty01 State) (target : Int)
    (s : State × Int) (q : b.d155.Ty20) :
    (b.d155.d158 target).d102 s (some q) = Sum.inl (b.d155.d102 s q) := rfl

theorem t389 (x y : Ty21) (f : Ty04) :
    d198 x (d199 y f) = d199 y (d198 x f) := rfl

theorem t390 {State R : Type} (a b : Ty01 State)
    (g : a.Ty19 → b.Ty19 → R) :
    ∃ c : Ty01 State, ∃ post : c.Ty19 → R, ∃ enc : a.Ty20 × b.Ty20 → c.Ty20,
      ∀ s p q, d187 a b g s p q = post (c.d102 s (enc (p, q))) :=
  ⟨a.d159 b, fun ans => g ans.1 ans.2, id, fun _ _ _ => rfl⟩

theorem t392 : Foam.Ty10.d172 d092 d097 ≠ Foam.Ty10.d172 d097 d092 := by decide

theorem t393 :
    (Foam.Ty08.d003 [true, false, false, false, false] true =
          Foam.Ty08.d003 [false, false, false, false, true] true ∧
        Foam.Ty08.d003 [true, false, false, false, false] false =
          Foam.Ty08.d003 [false, false, false, false, true] false) ∧
      (d197 [true, false, false, false, false] true =
          d197 [false, false, false, false, true] true ∧
        d197 [true, false, false, false, false] false =
          d197 [false, false, false, false, true] false) ∧
      [true, false, false, false, false] ≠ [false, false, false, false, true] :=
  ⟨⟨rfl, rfl⟩, ⟨by decide, by decide⟩, by decide⟩

theorem t394 {State : Type} (a b : Ty01 State)
    (s : State) (p : a.Ty20) (q : b.Ty20) :
    ((a.d159 b).d102 s (p, q)).1 = a.d102 s p := rfl

theorem t395 {State : Type} (a b : Ty01 State)
    (s : State) (p : a.Ty20) (q : b.Ty20) :
    ((a.d159 b).d102 s (p, q)).2 = b.d102 s q := rfl

theorem t396 (b : Ty01 State)
    (s : State) (n m : Int) :
    t076 b.d155.d102 (s, n) (s, m) :=
  fun _ => rfl

def d225 (n : Nat) : Ty15 (Ty13 n) (Ty13 (n + 1)) where
  d079       := Foam.Ty13.d127 n
  t158 := fun h => Foam.Ty13.t233 n h
  t157  := Foam.Ty13.t234 n

theorem t397 (f : Ty04) (za zb : Ty05) (h : za ≠ zb) :
    ((d190 (f, za)).2.d114 = (f, za).2.d114)
      ∧ (d190 (d190 (d190 (d190 (f, za)))) = (f, za))
      ∧ (t076 d194.d160.d102 (d190 (f, za)) (d190 (f, zb))
          ∧ d190 (f, za) ≠ d190 (f, zb))
      ∧ (∀ p, d194.d160.d102 (d190 (f, za)) p = d194.d160.d102 (f, za) p) :=
  ⟨t377 (f, za), t376 (f, za),
   t398 f za zb h, fun p => t378 d194 (f, za) p⟩

theorem t398 (f : Ty04) (za zb : Ty05) (h : za ≠ zb) :
    t076 d194.d160.d102 (d190 (f, za)) (d190 (f, zb))
      ∧ d190 (f, za) ≠ d190 (f, zb) :=
  ⟨fun _ => rfl, fun he => h (Foam.Ty05.t215 (congrArg Prod.snd he))⟩

theorem t399 :
    d194.d155.d157.t198 d194 ∧ d194.t198 d194.d155.d157 :=
  t374 d194

def d226 : Ty17 := ⟨d191, d192⟩
theorem t400 : t217 d029 (fun b => d141 b b) :=
  fun b _ => t320 b

theorem t401 [DecidableEq S] : ∀ (l : List S) (s : S),
    Foam.Ty05.d115 (d100 l s) = d098 l.length (Foam.Ty05.d110 (d197 l s)) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x l ih =>
    intro s
    have key : ∀ (W : Ty05), d098 (l.length + 1) (d098 3 W) = d098 l.length W := by
      intro W
      rw [t186]
      exact t185 l.length W
    show Foam.Ty05.d115 ((d098 l.length (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044)).d108 (d100 l s))
       = d098 (l.length + 1) (Foam.Ty05.d110 (d197 (x :: l) s))
    rw [t318, ih, t403, t268, t269, t270, t316, key]
    rfl

theorem t402 :
    (Foam.Ty08.d003 [true, false] true = Foam.Ty08.d003 [false, true] true ∧
        Foam.Ty08.d003 [true, false] false = Foam.Ty08.d003 [false, true] false) ∧
      d197 [true, false] true ≠ d197 [false, true] true :=
  ⟨⟨rfl, rfl⟩, by decide⟩

theorem t403 [DecidableEq S] (x : S) (l : List S) (s : S) :
    d197 (x :: l) s = (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (Foam.Ty05.d115 (d197 l s)) := rfl

theorem t404 (f : Ty04) (a b : Int) (hab : a ≠ b) :
    t076 d194.d155.d102 (f, a) (f, b) ∧ (f, a) ≠ (f, b) :=
  ⟨fun _ => rfl, fun h => hab (congrArg Prod.snd h)⟩

theorem t408 (x : Ty21) (f : Ty04) : (d198 x f).d106 = f.d106 := rfl
theorem t409 (y : Ty21) (f : Ty04) : (d199 y f).d105 = f.d105 := rfl

theorem t410 (l : List Ty21) :
    ∃ n, (d152 l).d033 n ≠ d186.d033 n :=
  t285 d144 l

theorem t411 :
    Foam.d202 1 0 1 0 = Foam.d202 0 1 0 1 ∧
    Foam.d204 1 0 1 0 = Foam.d204 0 1 0 1 ∧
    Foam.d203 1 0 1 0 = Foam.d203 0 1 0 1 ∧
    Foam.d201 1 0 1 0 ≠ Foam.d201 0 1 0 1 := by decide

theorem t412 (n0 n1 n2 n3 : Int) :
    Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3 = Foam.d001 (n0 + n2) := by
  rw [Foam.t419, Foam.t418, Foam.t002 n0 n1 n2 n3,
    Foam.t003 n0 n1 n2 n3, Foam.t090 (n0 + n2) (n1 + n3)]

theorem t413 :
    Foam.d204 1 1 1 1 = Foam.d204 0 0 0 0 ∧
    Foam.d203 1 1 1 1 = Foam.d203 0 0 0 0 ∧
    Foam.d201 1 1 1 1 = Foam.d201 0 0 0 0 ∧
    Foam.d202 1 1 1 1 ≠ Foam.d202 0 0 0 0 := by decide

theorem t414 (n0 n1 n2 n3 : Int) :
    Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3 = Foam.d001 (n1 + n3) := by
  rw [Foam.t419, Foam.t418, Foam.t002 n0 n1 n2 n3,
    Foam.t003 n0 n1 n2 n3, Foam.t089 (n0 + n2) (n1 + n3)]

theorem t415 :
    Foam.d202 0 1 0 0 = Foam.d202 0 0 0 1 ∧
    Foam.d204 0 1 0 0 = Foam.d204 0 0 0 1 ∧
    Foam.d201 0 1 0 0 = Foam.d201 0 0 0 1 ∧
    Foam.d203 0 1 0 0 ≠ Foam.d203 0 0 0 1 := by decide

theorem t416 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
        + Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n0) ∧
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
        + Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n1) ∧
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
        + -Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n2) ∧
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
        + -Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n3) :=
  ⟨Foam.t422 n0 n1 n2 n3, Foam.t423 n0 n1 n2 n3,
    Foam.t424 n0 n1 n2 n3, Foam.t425 n0 n1 n2 n3⟩

theorem t417 :
    Foam.d202 1 0 0 0 = Foam.d202 0 0 1 0 ∧
    Foam.d203 1 0 0 0 = Foam.d203 0 0 1 0 ∧
    Foam.d201 1 0 0 0 = Foam.d201 0 0 1 0 ∧
    Foam.d204 1 0 0 0 ≠ Foam.d204 0 0 1 0 := by decide

theorem t418 (n0 n1 n2 n3 : Int) :
    Foam.d201 n0 n1 n2 n3 = n0 + -n1 + n2 + -n3 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d031).d043 = n0 + -n1 + n2 + -n3
  rw [Foam.t349 n0 n1 n2 n3 Foam.d031]
  show (n0 * 1 + n1 * (-1)) + (n2 * 1 + n3 * (-1)) = n0 + -n1 + n2 + -n3
  rw [t020, t020, t019, t019, ← t005 (n0 + -n1) n2 (-n3)]

theorem t419 (n0 n1 n2 n3 : Int) :
    Foam.d202 n0 n1 n2 n3 = n0 + n1 + n2 + n3 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d032).d043 = n0 + n1 + n2 + n3
  rw [Foam.t349 n0 n1 n2 n3 Foam.d032]
  show (n0 * 1 + n1 * 1) + (n2 * 1 + n3 * 1) = n0 + n1 + n2 + n3
  rw [t020, t020, t020, t020, ← t005 (n0 + n1) n2 n3]

theorem t420 (n0 n1 n2 n3 : Int) :
    Foam.d203 n0 n1 n2 n3 = n1 + -n3 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d103).d041 = n1 + -n3
  rw [Foam.t348 n0 n1 n2 n3 Foam.d103]
  show (n0 * 0 + n1 * 1) + (n2 * 0 + n3 * (-1)) = n1 + -n3
  rw [t020, t022, t019, t022, t054, t054]

theorem t421 (n0 n1 n2 n3 : Int) :
    Foam.d204 n0 n1 n2 n3 = n0 + -n2 := by
  show (Foam.d163 n0 n1 n2 n3 Foam.d103).d043 = n0 + -n2
  rw [Foam.t349 n0 n1 n2 n3 Foam.d103]
  show (n0 * 1 + n1 * 0) + (n2 * (-1) + n3 * 0) = n0 + -n2
  rw [t020, t022, t019, t022, Int.add_zero, Int.add_zero]

theorem t422 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
      + Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n0) := by
  rw [Foam.t412, Foam.t421, ← Foam.t091 (n0 + n2) (n0 + -n2),
    Foam.t090 n0 n2]

theorem t423 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
      + Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n1) := by
  rw [Foam.t414, Foam.t420, ← Foam.t091 (n1 + n3) (n1 + -n3),
    Foam.t090 n1 n3]

theorem t424 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + Foam.d201 n0 n1 n2 n3)
      + -Foam.d001 (Foam.d204 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n2) := by
  rw [Foam.t412, Foam.t421, ← Foam.t092 (n0 + n2) (n0 + -n2),
    Foam.t089 n0 n2]

theorem t425 (n0 n1 n2 n3 : Int) :
    (Foam.d202 n0 n1 n2 n3 + -Foam.d201 n0 n1 n2 n3)
      + -Foam.d001 (Foam.d203 n0 n1 n2 n3) = Foam.d001 (Foam.d001 n3) := by
  rw [Foam.t414, Foam.t420, ← Foam.t092 (n1 + n3) (n1 + -n3),
    Foam.t089 n1 n3]

def t426 (bank : List (Ty01 State)) (q : Ty01 State) : Prop :=
  ¬ t354 bank q

theorem t099.t427 {bank bank' : List (Ty01 State)} {q : Ty01 State}
    (h : t099 bank q bank') : t354 bank' q :=
  ⟨q, h.t148, q.t332⟩

theorem Ty12.t428 (a b : Ty12) :
    a.d213 = b.d213 → a = b := by
  cases a <;> cases b <;> decide

theorem Ty12.t429 : Foam.Ty12.d213 Foam.Ty12.c2 = d092 := rfl

theorem Ty12.t430 (a b : Ty12) :
    (a * b).d213 = Foam.Ty10.d172 a.d213 b.d213 := by
  cases a <;> cases b <;> decide

theorem t100.t431 {walk bank : List (Ty01 State)} (h : t100 walk bank) :
    (∀ q ∈ walk, t354 bank q) ∧ t356 bank :=
  ⟨h.t432, h.t433⟩

theorem t100.t432 {walk bank : List (Ty01 State)} (h : t100 walk bank) :
    ∀ q ∈ walk, t354 bank q := by
  induction h with
  | c7 => intro q hq; cases hq
  | c8 q hrun hknown ih =>
      intro x hx
      cases hx with
      | head => exact hknown
      | tail _ hx' => exact ih x hx'
  | c9 q hrun hirr href ih =>
      intro x hx
      cases hx with
      | head => exact ⟨_, href.t148, Foam.Ty01.t332 _⟩
      | tail _ hx' =>
          obtain ⟨p, hp, hpx⟩ := ih x hx'
          rcases href.t357 p hp with hkeep | hcov
          · exact ⟨p, hkeep, hpx⟩
          · exact ⟨_, href.t148, Foam.Ty01.t333 hcov hpx⟩

theorem t100.t433 {walk bank : List (Ty01 State)} (h : t100 walk bank) :
    t356 bank := by
  induction h with
  | c7 => exact t473
  | c8 q hrun hknown ih => exact ih
  | c9 q hrun hirr href ih =>
      intro a ha b hb hab
      rcases href.t149 a ha with ha_eq | ha_old
      · rcases href.t149 b hb with hb_eq | hb_old
        · have heq : a = b := ha_eq.trans hb_eq.symm
          rw [heq]; exact Foam.Ty01.t332 b
        · rcases href.t358 b hb with hb_eq2 | hb_unc
          · have heq : a = b := ha_eq.trans hb_eq2.symm
            rw [heq]; exact Foam.Ty01.t332 b
          · rw [ha_eq] at hab
            exact absurd hab hb_unc
      · rcases href.t149 b hb with hb_eq | hb_old
        · rw [hb_eq] at hab
          exact absurd ⟨a, ha_old, hab⟩ hirr
        · exact ih a ha_old b hb_old hab

theorem Ty13.t434 (x y : Ty13 2) :
    Foam.Ty13.d129 (Foam.Ty13.d069 2 x y) = Foam.Ty09.d209 (Foam.Ty13.d129 x) (Foam.Ty13.d129 y) := rfl

theorem Ty13.t435 (s : Ty17) : Foam.Ty13.d180 (Foam.Ty17.d215 s) = s := rfl
theorem Ty16.t436 (S : Ty16 G) (o o' p : S.Ty24) :
    (S.d214 o).d051 p = (S.d214 o').d051 p * S.d133 o' o := by
  show S.d133 p o = S.d133 p o' * S.d133 o' o
  exact S.t250 p o' o

theorem Ty16.t437 (S : Ty16 G) (g : G) (p o : S.Ty24) :
    (S.d214 o).d051 (S.d131 g p) = g * (S.d214 o).d051 p := by
  show S.d133 (S.d131 g p) o = g * S.d133 p o
  have e : S.d131 (g * S.d133 p o) o = S.d131 g p := by
    rw [S.t239, S.t237 o p]
  have h := S.t249 (g * S.d133 p o) o
  rw [e] at h
  exact h

theorem Ty16.t438 (S : Ty16 G) (o o' : S.Ty24) (h : o ≠ o') :
    ∃ p, (S.d214 o).d051 p ≠ (S.d214 o').d051 p := by
  refine ⟨o, ?_⟩
  show S.d133 o o ≠ S.d133 o o'
  rw [S.t252]
  intro hbad
  apply h
  have h1 := S.t237 o' o
  rw [← hbad, S.t241] at h1
  exact h1.symm

def Ty17.d227 (X Y : Ty17) : Ty17 :=
  ⟨Foam.Ty09.d210 (Foam.Ty09.d209 X.d081 Y.d081) (Foam.Ty09.d209 (Foam.Ty09.d208 Y.d082) X.d082),
   Foam.Ty09.d207 (Foam.Ty09.d209 Y.d082 X.d081) (Foam.Ty09.d209 X.d082 (Foam.Ty09.d208 Y.d081))⟩

theorem Ty17.t439 (x : Ty13 3) : Foam.Ty17.d215 (Foam.Ty13.d180 x) = x := rfl

theorem Ty28.t440 {X S T : Ty18} (f : Ty28 X S) (g : Ty28 X T) :
    (Foam.Ty28.d217 S T).d185 (Foam.Ty28.d218 f g) = f := rfl

theorem Ty28.t441 {X S T : Ty18} (h : Ty28 X (Foam.Ty18.d184 S T)) :
    h = Foam.Ty28.d218 ((Foam.Ty28.d217 S T).d185 h) ((Foam.Ty28.d219 S T).d185 h) := rfl

theorem Ty28.t442 {X S T : Ty18} (f : Ty28 X S) (g : Ty28 X T) :
    (Foam.Ty28.d219 S T).d185 (Foam.Ty28.d218 f g) = g := rfl

theorem t443 {l l' : List Ty21} (h : d220.d079 l = d220.d079 l') : l = l' :=
  d220.t158 h

theorem t444 :
    ¬ ∃ g : Ty02 Ty21 → List Ty21, ∀ c, d220.d079 (g c) = c :=
  d220.t159

theorem t445 :
    (t205 (d198 d145) d194 ∧ t205 (d199 d145) d194)
      ∧ (t359 d198 d023 ∧ t359 d199 d024)
      ∧ (∀ x y f, d198 x (d199 y f) = d199 y (d198 x f))
      ∧ (∀ n, (d194.d200 n).t198 d194 ∧ d194.t198 (d194.d200 n)) :=
  ⟨t381, t474, t389, t475⟩

theorem t451 (b : Ty01 State) (m n : Nat) :
    (b.d200 (n + m)).t198 (b.d200 m) ∧
      (b.d200 m).t198 (b.d200 (n + m)) :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

theorem t452 (b : Ty01 State) (n : Nat) :
    (b.d200 n).t198 (b.d200 n) ∧
      (b.d200 n).t198 b ∧ b.t198 (b.d200 n) :=
  ⟨Foam.Ty01.t332 _, t453 b n⟩

theorem t453 (b : Ty01 State) (n : Nat) :
    (b.d200 n).t198 b ∧ b.t198 (b.d200 n) :=
  ⟨⟨id, id, fun _ _ => rfl⟩, ⟨id, id, fun _ _ => rfl⟩⟩

theorem t454 : Foam.Ty09.d209 d191 d188 ≠ Foam.Ty09.d209 d188 d191 := by decide

theorem t455 : Foam.Ty09.d209 d188 d188 = Foam.Ty09.d166 := by decide

theorem t456 (S : Ty18) (p : S.Ty26) :
    (d143 S).d185 (d223 S p) = d143 (d196 S p) := rfl

theorem t457 (S : Ty18) (p : S.Ty26) :
    (d223 S p).d138 () = p := rfl

theorem t458 (b : Ty01 State) (n : Nat) (s : State) (p : b.Ty20) :
    (b.d200 n).d102 s p = b.d102 s p := rfl

theorem t461 : Foam.Ty10.d172 (Foam.Ty10.d172 d092 d097) d224 = Foam.Ty10.d059 := by decide

theorem t462 : (d225 0).t160 (Foam.Ty10.d122 d097) :=
  fun x => t301 x

def d228 : Ty09 := ⟨d224, Foam.Ty10.d123⟩
theorem t463 : Foam.Ty10.d172 d224 d224 = Foam.Ty10.d059 := by decide

theorem t465 (f : Ty04) (a b : Int) (hab : a ≠ b) :
    (t076 d194.d155.d102 (f, a) (f, b) ∧ (f, a) ≠ (f, b))
      ∧ (¬ ∃ p, d194.d155.d102 (f, a) p ≠ d194.d155.d102 (f, b) p)
      ∧ (¬ ∃ g : Ty02 Ty21 → List Ty21, ∀ c, d220.d079 (g c) = c) :=
  ⟨t404 f a b hab, t380 f a b, d220.t159⟩

theorem t466 :
    Foam.Ty09.d209 (Foam.Ty09.d209 d191 d192) d188 ≠ Foam.Ty09.d209 d191 (Foam.Ty09.d209 d192 d188) := by decide

theorem t468 (x : Ty21) (f : Ty04) :
    d194.d102 (d221 (d198 x f)) d024 = x := rfl

theorem t473 : t356 ([] : List (Ty01 State)) := by
  intro a ha; cases ha

theorem t474 : t359 d198 d023 ∧ t359 d199 d024 :=
  ⟨⟨id, fun _ _ => rfl⟩, ⟨id, fun _ _ => rfl⟩⟩

theorem t475 (n : Nat) :
    (d194.d200 n).t198 d194 ∧ d194.t198 (d194.d200 n) :=
  t453 d194 n

theorem t476 : d226 ≠ Foam.Ty17.d216 := by decide

theorem t477 : d195 ≠ Foam.Ty17.d216 := by decide

theorem t478 {S C : Type} [DecidableEq S] (refresh : List S → C → C) :
    t217 (d206 S C) (fun st => (st.1, refresh st.1 st.2)) :=
  fun _ _ => rfl

theorem t479 {S C : Type} [DecidableEq S] (refresh : List S → C → C)
    (ps : List S) (st : List S × C) :
    d154 (d206 S C) (fun st => (st.1, refresh st.1 st.2)) st ps
      = d153 (d206 S C) st ps :=
  t386 _ _ (t478 refresh) ps st

theorem t480 :
    Foam.Ty10.d172 d092 d092 = Foam.Ty10.d059
      ∧ Foam.Ty10.d172 d097 d097 = Foam.Ty10.d059
      ∧ Foam.Ty10.d172 d224 d224 = Foam.Ty10.d059 :=
  ⟨t379, t384, t463⟩

theorem t481 : Foam.Ty10.d172 d097 d092 = Foam.Ty10.d172 Foam.Ty10.d059 d224 := by decide

theorem t482 :
    Foam.Ty10.d172 d092 d097 = d224
      ∧ Foam.Ty10.d172 d097 d224 = d092
      ∧ Foam.Ty10.d172 d224 d092 = d097 := by decide

theorem Ty13.t483 (x y : Ty13 3) :
    Foam.Ty13.d180 (Foam.Ty13.d069 3 x y) = Foam.Ty17.d227 (Foam.Ty13.d180 x) (Foam.Ty13.d180 y) := rfl

theorem t484 :
    Foam.Ty17.d227 d226 d195 = Foam.Ty17.d216 ∧ d226 ≠ Foam.Ty17.d216 ∧ d195 ≠ Foam.Ty17.d216 :=
  ⟨t489, t476, t477⟩

theorem t485 : Foam.Ty09.d209 (Foam.Ty09.d209 d191 d192) d228 = Foam.Ty09.d166 := by decide

theorem t488 (q : Ty01 State) : t426 [] q := by
  rintro ⟨p, hp, _⟩
  cases hp

theorem t489 : Foam.Ty17.d227 d226 d195 = Foam.Ty17.d216 := by decide


/-- info: 'Foam.t270' does not depend on any axioms -/
#guard_msgs in #print axioms t270
/-- info: 'Foam.t187' does not depend on any axioms -/
#guard_msgs in #print axioms t187
/-- info: 'Foam.t401' does not depend on any axioms -/
#guard_msgs in #print axioms t401
/-- info: 'Foam.t115' does not depend on any axioms -/
#guard_msgs in #print axioms t115
/-- info: 'Foam.t116' does not depend on any axioms -/
#guard_msgs in #print axioms t116
/-- info: 'Foam.t166' does not depend on any axioms -/
#guard_msgs in #print axioms t166
/-- info: 'Foam.t385' does not depend on any axioms -/
#guard_msgs in #print axioms t385
/-- info: 'Foam.t111' does not depend on any axioms -/
#guard_msgs in #print axioms t111
/-- info: 'Foam.t110' does not depend on any axioms -/
#guard_msgs in #print axioms t110
/-- info: 'Foam.t109' does not depend on any axioms -/
#guard_msgs in #print axioms t109
/-- info: 'Foam.t088' does not depend on any axioms -/
#guard_msgs in #print axioms t088
/-- info: 'Foam.t170' does not depend on any axioms -/
#guard_msgs in #print axioms t170
/-- info: 'Foam.t114' does not depend on any axioms -/
#guard_msgs in #print axioms t114
/-- info: 'Foam.t171' does not depend on any axioms -/
#guard_msgs in #print axioms t171
/-- info: 'Foam.t133' does not depend on any axioms -/
#guard_msgs in #print axioms t133
/-- info: 'Foam.t123' does not depend on any axioms -/
#guard_msgs in #print axioms t123
/-- info: 'Foam.t168' does not depend on any axioms -/
#guard_msgs in #print axioms t168
/-- info: 'Foam.t402' does not depend on any axioms -/
#guard_msgs in #print axioms t402
/-- info: 'Foam.t259' does not depend on any axioms -/
#guard_msgs in #print axioms t259
/-- info: 'Foam.t261' does not depend on any axioms -/
#guard_msgs in #print axioms t261
/-- info: 'Foam.t393' does not depend on any axioms -/
#guard_msgs in #print axioms t393
/-- info: 'Foam.t131' does not depend on any axioms -/
#guard_msgs in #print axioms t131
/-- info: 'Foam.t189' does not depend on any axioms -/
#guard_msgs in #print axioms t189
/-- info: 'Foam.t070' does not depend on any axioms -/
#guard_msgs in #print axioms t070
/-- info: 'Foam.t071' does not depend on any axioms -/
#guard_msgs in #print axioms t071
/-- info: 'Foam.t188' does not depend on any axioms -/
#guard_msgs in #print axioms t188
/-- info: 'Foam.t307' does not depend on any axioms -/
#guard_msgs in #print axioms t307
/-- info: 'Foam.t118' does not depend on any axioms -/
#guard_msgs in #print axioms t118
/-- info: 'Foam.t197' does not depend on any axioms -/
#guard_msgs in #print axioms t197
/-- info: 'Foam.t167' does not depend on any axioms -/
#guard_msgs in #print axioms t167
/-- info: 'Foam.t162' does not depend on any axioms -/
#guard_msgs in #print axioms t162
/-- info: 'Foam.t323' does not depend on any axioms -/
#guard_msgs in #print axioms t323
/-- info: 'Foam.t163' does not depend on any axioms -/
#guard_msgs in #print axioms t163
/-- info: 'Foam.t103' does not depend on any axioms -/
#guard_msgs in #print axioms t103
/-- info: 'Foam.t102' does not depend on any axioms -/
#guard_msgs in #print axioms t102
/-- info: 'Foam.t113' does not depend on any axioms -/
#guard_msgs in #print axioms t113
/-- info: 'Foam.t112' does not depend on any axioms -/
#guard_msgs in #print axioms t112
/-- info: 'Foam.t478' does not depend on any axioms -/
#guard_msgs in #print axioms t478
/-- info: 'Foam.t479' does not depend on any axioms -/
#guard_msgs in #print axioms t479
/-- info: 'Foam.t161' does not depend on any axioms -/
#guard_msgs in #print axioms t161
/-- info: 'Foam.t181' does not depend on any axioms -/
#guard_msgs in #print axioms t181
/-- info: 'Foam.Ty08.t093' does not depend on any axioms -/
#guard_msgs in #print axioms Ty08.t093
/-- info: 'Foam.Ty08.t094' does not depend on any axioms -/
#guard_msgs in #print axioms Ty08.t094
/-- info: 'Foam.t382' does not depend on any axioms -/
#guard_msgs in #print axioms t382
/-- info: 'Foam.t327' does not depend on any axioms -/
#guard_msgs in #print axioms t327
/-- info: 'Foam.t386' does not depend on any axioms -/
#guard_msgs in #print axioms t386
/-- info: 'Foam.t320' does not depend on any axioms -/
#guard_msgs in #print axioms t320
/-- info: 'Foam.t164' does not depend on any axioms -/
#guard_msgs in #print axioms t164
/-- info: 'Foam.t400' does not depend on any axioms -/
#guard_msgs in #print axioms t400
/-- info: 'Foam.t371' does not depend on any axioms -/
#guard_msgs in #print axioms t371
/-- info: 'Foam.t370' does not depend on any axioms -/
#guard_msgs in #print axioms t370
/-- info: 'Foam.t458' does not depend on any axioms -/
#guard_msgs in #print axioms t458
/-- info: 'Foam.t453' does not depend on any axioms -/
#guard_msgs in #print axioms t453
/-- info: 'Foam.t452' does not depend on any axioms -/
#guard_msgs in #print axioms t452
/-- info: 'Foam.t451' does not depend on any axioms -/
#guard_msgs in #print axioms t451
/-- info: 'Foam.t117' does not depend on any axioms -/
#guard_msgs in #print axioms t117
/-- info: 'Foam.t135' does not depend on any axioms -/
#guard_msgs in #print axioms t135
/-- info: 'Foam.t104' does not depend on any axioms -/
#guard_msgs in #print axioms t104
/-- info: 'Foam.t105' does not depend on any axioms -/
#guard_msgs in #print axioms t105
/-- info: 'Foam.t191' does not depend on any axioms -/
#guard_msgs in #print axioms t191
/-- info: 'Foam.t374' does not depend on any axioms -/
#guard_msgs in #print axioms t374
/-- info: 'Foam.t373' does not depend on any axioms -/
#guard_msgs in #print axioms t373
/-- info: 'Foam.t372' does not depend on any axioms -/
#guard_msgs in #print axioms t372
/-- info: 'Foam.t264' does not depend on any axioms -/
#guard_msgs in #print axioms t264
/-- info: 'Foam.t396' does not depend on any axioms -/
#guard_msgs in #print axioms t396
/-- info: 'Foam.t314' does not depend on any axioms -/
#guard_msgs in #print axioms t314
/-- info: 'Foam.t072' does not depend on any axioms -/
#guard_msgs in #print axioms t072
/-- info: 'Foam.t388' does not depend on any axioms -/
#guard_msgs in #print axioms t388
/-- info: 'Foam.t387' does not depend on any axioms -/
#guard_msgs in #print axioms t387
/-- info: 'Foam.t193' does not depend on any axioms -/
#guard_msgs in #print axioms t193
/-- info: 'Foam.t195' does not depend on any axioms -/
#guard_msgs in #print axioms t195
/-- info: 'Foam.t169' does not depend on any axioms -/
#guard_msgs in #print axioms t169
/-- info: 'Foam.t108' does not depend on any axioms -/
#guard_msgs in #print axioms t108
/-- info: 'Foam.t086' does not depend on any axioms -/
#guard_msgs in #print axioms t086
/-- info: 'Foam.t087' does not depend on any axioms -/
#guard_msgs in #print axioms t087
/-- info: 'Foam.t106' does not depend on any axioms -/
#guard_msgs in #print axioms t106
/-- info: 'Foam.t127' does not depend on any axioms -/
#guard_msgs in #print axioms t127
/-- info: 'Foam.t310' does not depend on any axioms -/
#guard_msgs in #print axioms t310
/-- info: 'Foam.t394' does not depend on any axioms -/
#guard_msgs in #print axioms t394
/-- info: 'Foam.t395' does not depend on any axioms -/
#guard_msgs in #print axioms t395
/-- info: 'Foam.t369' does not depend on any axioms -/
#guard_msgs in #print axioms t369
/-- info: 'Foam.t390' does not depend on any axioms -/
#guard_msgs in #print axioms t390
/-- info: 'Foam.Ty18.t362' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty18.t362
/-- info: 'Foam.Ty01.t334' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty01.t334
/-- info: 'Foam.Ty12.t430' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t430
/-- info: 'Foam.Ty12.t428' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t428
/-- info: 'Foam.Ty05.t351' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t351
/-- info: 'Foam.Ty05.t216' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t216
/-- info: 'Foam.Ty05.t208' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t208
/-- info: 'Foam.Ty05.t353' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t353
/-- info: 'Foam.Ty05.t352' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t352
/-- info: 'Foam.t203' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t203
/-- info: 'Foam.t199' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t199
/-- info: 'Foam.t201' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t201
/-- info: 'Foam.t338' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t338
/-- info: 'Foam.t204' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t204
/-- info: 'Foam.t200' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t200
/-- info: 'Foam.t202' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t202
/-- info: 'Foam.t340' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t340
/-- info: 'Foam.t347' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t347
/-- info: 'Foam.t337' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t337
/-- info: 'Foam.t343' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t343
/-- info: 'Foam.t339' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t339
/-- info: 'Foam.t344' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t344
/-- info: 'Foam.t346' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t346
/-- info: 'Foam.t345' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t345
/-- info: 'Foam.t336' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t336
/-- info: 'Foam.t335' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t335
/-- info: 'Foam.t341' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t341
/-- info: 'Foam.t342' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t342
/-- info: 'Foam.t136' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t136
/-- info: 'Foam.Ty05.t209' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t209
/-- info: 'Foam.t349' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t349
/-- info: 'Foam.t348' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t348
/-- info: 'Foam.t419' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t419
/-- info: 'Foam.t418' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t418
/-- info: 'Foam.t421' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t421
/-- info: 'Foam.t420' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t420
/-- info: 'Foam.t002' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t002
/-- info: 'Foam.t003' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t003
/-- info: 'Foam.t090' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t090
/-- info: 'Foam.t089' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t089
/-- info: 'Foam.t091' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t091
/-- info: 'Foam.t092' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t092
/-- info: 'Foam.t412' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t412
/-- info: 'Foam.t414' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t414
/-- info: 'Foam.t422' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t422
/-- info: 'Foam.t423' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t423
/-- info: 'Foam.t424' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t424
/-- info: 'Foam.t425' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t425
/-- info: 'Foam.t416' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t416
/-- info: 'Foam.t413' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t413
/-- info: 'Foam.t417' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t417
/-- info: 'Foam.t415' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t415
/-- info: 'Foam.t411' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t411
/-- info: 'Foam.Ty12.t150' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t150
/-- info: 'Foam.t174' does not depend on any axioms -/
#guard_msgs in #print axioms t174
/-- info: 'Foam.t273' does not depend on any axioms -/
#guard_msgs in #print axioms t273
/-- info: 'Foam.t175' does not depend on any axioms -/
#guard_msgs in #print axioms t175
/-- info: 'Foam.Ty05.t210' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t210
/-- info: 'Foam.Ty05.t214' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t214
/-- info: 'Foam.t260' does not depend on any axioms -/
#guard_msgs in #print axioms t260
/-- info: 'Foam.t322' does not depend on any axioms -/
#guard_msgs in #print axioms t322
/-- info: 'Foam.t266' does not depend on any axioms -/
#guard_msgs in #print axioms t266
/-- info: 'Foam.t265' does not depend on any axioms -/
#guard_msgs in #print axioms t265
/-- info: 'Foam.t404' does not depend on any axioms -/
#guard_msgs in #print axioms t404
/-- info: 'Foam.t380' does not depend on any axioms -/
#guard_msgs in #print axioms t380
/-- info: 'Foam.t468' does not depend on any axioms -/
#guard_msgs in #print axioms t468
/-- info: 'Foam.t443' does not depend on any axioms -/
#guard_msgs in #print axioms t443
/-- info: 'Foam.t444' does not depend on any axioms -/
#guard_msgs in #print axioms t444
/-- info: 'Foam.t410' does not depend on any axioms -/
#guard_msgs in #print axioms t410
/-- info: 'Foam.t465' does not depend on any axioms -/
#guard_msgs in #print axioms t465
/-- info: 'Foam.Ty12.t228' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t228
/-- info: 'Foam.Ty12.t229' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t229
/-- info: 'Foam.Ty12.t230' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty12.t230
/-- info: 'Foam.Ty05.t213' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t213
/-- info: 'Foam.t384' does not depend on any axioms -/
#guard_msgs in #print axioms t384
/-- info: 'Foam.t392' does not depend on any axioms -/
#guard_msgs in #print axioms t392
/-- info: 'Foam.t480' does not depend on any axioms -/
#guard_msgs in #print axioms t480
/-- info: 'Foam.Ty01.t332' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty01.t332
/-- info: 'Foam.Ty01.t333' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty01.t333
/-- info: 'Foam.t488' does not depend on any axioms -/
#guard_msgs in #print axioms t488
/-- info: 'Foam.t099.t427' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t099.t427
/-- info: 'Foam.t100.t432' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t100.t432
/-- info: 'Foam.t100.t433' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t100.t433
/-- info: 'Foam.t100.t431' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t100.t431
/-- info: 'Foam.Ty13.t233' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t233
/-- info: 'Foam.Ty13.t156' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t156
/-- info: 'Foam.Ty13.t234' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t234
/-- info: 'Foam.t301' does not depend on any axioms -/
#guard_msgs in #print axioms t301
/-- info: 'Foam.t462' does not depend on any axioms -/
#guard_msgs in #print axioms t462
/-- info: 'Foam.t267' does not depend on any axioms -/
#guard_msgs in #print axioms t267
/-- info: 'Foam.t276' does not depend on any axioms -/
#guard_msgs in #print axioms t276
/-- info: 'Foam.t302' does not depend on any axioms -/
#guard_msgs in #print axioms t302
/-- info: 'Foam.t275' does not depend on any axioms -/
#guard_msgs in #print axioms t275
/-- info: 'Foam.t367' does not depend on any axioms -/
#guard_msgs in #print axioms t367
/-- info: 'Foam.t283' does not depend on any axioms -/
#guard_msgs in #print axioms t283
/-- info: 'Foam.Ty16.d181' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.d181
/-- info: 'Foam.Ty16.t238' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t238
/-- info: 'Foam.Ty13.t235' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t235
/-- info: 'Foam.Ty13.t232' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t232
/-- info: 'Foam.Ty13.t361' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t361
/-- info: 'Foam.Ty10.t226' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty10.t226
/-- info: 'Foam.Ty13.t434' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t434
/-- info: 'Foam.Ty09.t355' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty09.t355
/-- info: 'Foam.Ty13.t483' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t483
/-- info: 'Foam.Ty17.t439' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty17.t439
/-- info: 'Foam.t190' does not depend on any axioms -/
#guard_msgs in #print axioms t190
/-- info: 'Foam.Ty16.t244' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t244
/-- info: 'Foam.Ty16.t242' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t242
/-- info: 'Foam.Ty16.t254' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t254
/-- info: 'Foam.Ty16.t243' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t243
/-- info: 'Foam.t130' does not depend on any axioms -/
#guard_msgs in #print axioms t130
/-- info: 'Foam.t129' does not depend on any axioms -/
#guard_msgs in #print axioms t129
/-- info: 'Foam.t101' does not depend on any axioms -/
#guard_msgs in #print axioms t101
/-- info: 'Foam.t122' does not depend on any axioms -/
#guard_msgs in #print axioms t122
/-- info: 'Foam.t120' does not depend on any axioms -/
#guard_msgs in #print axioms t120
/-- info: 'Foam.t121' does not depend on any axioms -/
#guard_msgs in #print axioms t121
/-- info: 'Foam.t134' does not depend on any axioms -/
#guard_msgs in #print axioms t134
/-- info: 'Foam.t132' does not depend on any axioms -/
#guard_msgs in #print axioms t132
/-- info: 'Foam.t062' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t062
/-- info: 'Foam.Ty05.t211' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t211
/-- info: 'Foam.Ty05.t212' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t212
/-- info: 'Foam.Ty28.t365' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t365
/-- info: 'Foam.Ty28.t363' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t363
/-- info: 'Foam.Ty28.t440' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t440
/-- info: 'Foam.Ty28.t442' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t442
/-- info: 'Foam.Ty28.t441' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t441
/-- info: 'Foam.Ty22.d205' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty22.d205
/-- info: 'Foam.t069.t098' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t069.t098
/-- info: 'Foam.t068.t096' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t068.t096
/-- info: 'Foam.t128' does not depend on any axioms -/
#guard_msgs in #print axioms t128
/-- info: 'Foam.d151' does not depend on any axioms -/
#guard_msgs in #print axioms d151
/-- info: 'Foam.t485' does not depend on any axioms -/
#guard_msgs in #print axioms t485
/-- info: 'Foam.t455' does not depend on any axioms -/
#guard_msgs in #print axioms t455
/-- info: 'Foam.t466' does not depend on any axioms -/
#guard_msgs in #print axioms t466
/-- info: 'Foam.Ty23.t223' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t223
/-- info: 'Foam.Ty23.t219' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t219
/-- info: 'Foam.Ty23.t218' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t218
/-- info: 'Foam.Ty23.t221' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t221
/-- info: 'Foam.t182' does not depend on any axioms -/
#guard_msgs in #print axioms t182
/-- info: 'Foam.Ty23.t225' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t225
/-- info: 'Foam.Ty23.t224' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t224
/-- info: 'Foam.Ty11.t147' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty11.t147
/-- info: 'Foam.t282' does not depend on any axioms -/
#guard_msgs in #print axioms t282
/-- info: 'Foam.t381' does not depend on any axioms -/
#guard_msgs in #print axioms t381
/-- info: 'Foam.t474' does not depend on any axioms -/
#guard_msgs in #print axioms t474
/-- info: 'Foam.t389' does not depend on any axioms -/
#guard_msgs in #print axioms t389
/-- info: 'Foam.t399' does not depend on any axioms -/
#guard_msgs in #print axioms t399
/-- info: 'Foam.t475' does not depend on any axioms -/
#guard_msgs in #print axioms t475
/-- info: 'Foam.t445' does not depend on any axioms -/
#guard_msgs in #print axioms t445
/-- info: 'Foam.Ty16.t253' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t253
/-- info: 'Foam.Ty16.t245' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t245
/-- info: 'Foam.Ty16.t246' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t246
/-- info: 'Foam.t279' does not depend on any axioms -/
#guard_msgs in #print axioms t279
/-- info: 'Foam.t165' does not depend on any axioms -/
#guard_msgs in #print axioms t165
/-- info: 'Foam.t308' does not depend on any axioms -/
#guard_msgs in #print axioms t308
/-- info: 'Foam.t309' does not depend on any axioms -/
#guard_msgs in #print axioms t309
/-- info: 'Foam.t077' does not depend on any axioms -/
#guard_msgs in #print axioms t077
/-- info: 'Foam.t083' does not depend on any axioms -/
#guard_msgs in #print axioms t083
/-- info: 'Foam.t080' does not depend on any axioms -/
#guard_msgs in #print axioms t080
/-- info: 'Foam.t081' does not depend on any axioms -/
#guard_msgs in #print axioms t081
/-- info: 'Foam.t298' does not depend on any axioms -/
#guard_msgs in #print axioms t298
/-- info: 'Foam.Ty05.t215' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t215
/-- info: 'Foam.t280' does not depend on any axioms -/
#guard_msgs in #print axioms t280
/-- info: 'Foam.t378' does not depend on any axioms -/
#guard_msgs in #print axioms t378
/-- info: 'Foam.t377' does not depend on any axioms -/
#guard_msgs in #print axioms t377
/-- info: 'Foam.t376' does not depend on any axioms -/
#guard_msgs in #print axioms t376
/-- info: 'Foam.t398' does not depend on any axioms -/
#guard_msgs in #print axioms t398
/-- info: 'Foam.t366' does not depend on any axioms -/
#guard_msgs in #print axioms t366
/-- info: 'Foam.t277' does not depend on any axioms -/
#guard_msgs in #print axioms t277
/-- info: 'Foam.t397' does not depend on any axioms -/
#guard_msgs in #print axioms t397
/-- info: 'Foam.Ty15.t159' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty15.t159
/-- info: 'Foam.d193' does not depend on any axioms -/
#guard_msgs in #print axioms d193
/-- info: 'Foam.t311' does not depend on any axioms -/
#guard_msgs in #print axioms t311
/-- info: 'Foam.t312' does not depend on any axioms -/
#guard_msgs in #print axioms t312
/-- info: 'Foam.t319' does not depend on any axioms -/
#guard_msgs in #print axioms t319
/-- info: 'Foam.t484' does not depend on any axioms -/
#guard_msgs in #print axioms t484
/-- info: 'Foam.t289' does not depend on any axioms -/
#guard_msgs in #print axioms t289
/-- info: 'Foam.t290' does not depend on any axioms -/
#guard_msgs in #print axioms t290
/-- info: 'Foam.t079' does not depend on any axioms -/
#guard_msgs in #print axioms t079
/-- info: 'Foam.t299' does not depend on any axioms -/
#guard_msgs in #print axioms t299
/-- info: 'Foam.t300' does not depend on any axioms -/
#guard_msgs in #print axioms t300
/-- info: 'Foam.t284' does not depend on any axioms -/
#guard_msgs in #print axioms t284
/-- info: 'Foam.t331' does not depend on any axioms -/
#guard_msgs in #print axioms t331
/-- info: 'Foam.t305' does not depend on any axioms -/
#guard_msgs in #print axioms t305
/-- info: 'Foam.Ty16.t240' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t240
/-- info: 'Foam.d223' does not depend on any axioms -/
#guard_msgs in #print axioms d223
/-- info: 'Foam.t375' does not depend on any axioms -/
#guard_msgs in #print axioms t375
/-- info: 'Foam.t457' does not depend on any axioms -/
#guard_msgs in #print axioms t457
/-- info: 'Foam.t281' does not depend on any axioms -/
#guard_msgs in #print axioms t281
/-- info: 'Foam.t456' does not depend on any axioms -/
#guard_msgs in #print axioms t456
/-- info: 'Foam.t482' does not depend on any axioms -/
#guard_msgs in #print axioms t482
/-- info: 'Foam.t481' does not depend on any axioms -/
#guard_msgs in #print axioms t481
/-- info: 'Foam.t461' does not depend on any axioms -/
#guard_msgs in #print axioms t461
/-- info: 'Foam.Ty16.t252' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t252
/-- info: 'Foam.Ty16.t251' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t251
/-- info: 'Foam.Ty16.t250' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t250
/-- info: 'Foam.Ty16.t437' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t437
/-- info: 'Foam.Ty16.t436' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t436
/-- info: 'Foam.Ty16.t438' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty16.t438

end Foam
