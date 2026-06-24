/-!
# Axiom-free `Int` ring foundations

Core's `Int` ring lemmas (`Int.add_comm`, `Int.add_assoc`, `Int.mul_comm`,
`Int.mul_assoc`, `Int.add_mul`, `Int.mul_add`, `Int.add_right_neg`, ...) each
depend on `propext`. This module re-derives the ones foam's measurement layer
needs entirely axiom-free: by case-splitting on the `Int.ofNat`/`Int.negSucc`
constructors and reducing to axiom-free `Nat` lemmas. Everything here is verified
`does not depend on any axioms`.
-/

namespace Foam

theorem t011 (m n : Nat) : (m + n) - n = m := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, Nat.succ_sub_succ]; exact ih
theorem t012 (m n : Nat) : (m + n) - m = n := by
  rw [Nat.add_comm]; exact t011 n m
theorem t049 {m n : Nat} (h : m ≤ n) : m - n = 0 := by
  induction h with
  | refl => exact Nat.sub_self m
  | step _ ih => rw [Nat.sub_succ, ih]; rfl
theorem t043 {m n : Nat} (h : n ≤ m) : Int.subNatNat m n = Int.ofNat (m - n) := by
  show (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ k => Int.negSucc k) = Int.ofNat (m - n)
  rw [t049 h]
theorem t042 (m d : Nat) : Int.subNatNat m (m + d + 1) = Int.negSucc d := by
  show (match (m+d+1) - m with | 0 => Int.ofNat (m - (m+d+1)) | Nat.succ k => Int.negSucc k) = Int.negSucc d
  have h : (m + d + 1) - m = d + 1 := by rw [Nat.add_assoc m d 1, t012]
  rw [h]
theorem t047 (m n : Nat) :
    Int.subNatNat (m+1) (n+1) = Int.subNatNat m n := by
  show (match (n+1) - (m+1) with | 0 => Int.ofNat ((m+1) - (n+1)) | Nat.succ c => Int.negSucc c)
     = (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ c => Int.negSucc c)
  rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
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
theorem t036 (a : Nat) (s : Int) :
    Int.ofNat (a+1) + s = (Int.ofNat a + s) + 1 := by
  cases s with
  | ofNat j =>
    show Int.ofNat ((a+1)+j) = Int.ofNat (a+j) + 1
    rw [show (a+1)+j = (a+j)+1 from by rw [Nat.add_right_comm a 1 j]]; rfl
  | negSucc j =>
    show Int.subNatNat (a+1) (j+1) = Int.subNatNat a (j+1) + 1
    rw [t047 a j, t046 a j]
theorem t054 (a : Int) : 0 + a = a := by
  cases a with
  | ofNat n => show Int.ofNat (0 + n) = Int.ofNat n; rw [Nat.zero_add]
  | negSucc n => rfl
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
theorem t038 (m n k : Nat) :
    Int.subNatNat (m + n) k = Int.ofNat m + Int.subNatNat n k := by
  induction m with
  | zero => rw [Nat.zero_add, show Int.ofNat 0 = (0:Int) from rfl, t054]
  | succ a ih =>
    rw [Nat.succ_add, t045 (a+n) k, ih]
    exact (t036 a (Int.subNatNat n k)).symm
theorem t009 (k m n : Nat) : (k + m) - (k + n) = m - n := by
  induction k with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ d ih =>
    rw [show d+1+m = (d+m)+1 from by rw [Nat.add_right_comm d 1 m],
        show d+1+n = (d+n)+1 from by rw [Nat.add_right_comm d 1 n],
        Nat.succ_sub_succ]; exact ih
theorem t010 (m k n : Nat) : (m + k) - (n + k) = m - n := by
  rw [Nat.add_comm m k, Nat.add_comm n k]; exact t009 k m n
theorem t039 (m n k : Nat) :
    Int.subNatNat (m + k) (n + k) = Int.subNatNat m n := by
  show (match (n+k) - (m+k) with | 0 => Int.ofNat ((m+k) - (n+k)) | Nat.succ c => Int.negSucc c)
     = (match n - m with | 0 => Int.ofNat (m - n) | Nat.succ c => Int.negSucc c)
  rw [t010 n k m, t010 m k n]
theorem t004 (a b : Int) : a + b = b + a := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => show Int.ofNat (m + n) = Int.ofNat (n + m); rw [Nat.add_comm]
    | negSucc n => rfl
  | negSucc m => cases b with
    | ofNat n => rfl
    | negSucc n => show Int.negSucc (m + n).succ = Int.negSucc (n + m).succ; rw [Nat.add_comm]
theorem t041 (m n k : Nat) :
    Int.subNatNat m n + Int.ofNat k = Int.subNatNat (m + k) n := by
  rw [Nat.add_comm m k, t038 k m n, t004]
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
theorem t006 (a : Int) : (-a) + a = 0 := by
  rw [t004]; exact t008 a
theorem t026 {a b : Int} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← t005, t006, t054]
theorem t025 (a b : Int) : -(a + b) = -a + -b := by
  apply t026
  rw [t005, t004 (-a) (-b), ← t005 b (-b) (-a), t008, t054, t008]
theorem t044 {m n : Nat} (h : m < n) : Int.subNatNat m n = -(Int.ofNat (n - m)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [show Int.subNatNat m (m+1+d) = Int.negSucc d from by
        rw [show m+1+d = m+d+1 from by rw [Nat.add_right_comm m 1 d]]; exact t042 m d]
  rw [show (m+1+d) - m = d+1 from by
        rw [Nat.add_right_comm m 1 d, Nat.add_assoc m d 1, t012]]
  rfl
theorem t014 (a b : Int) : a * b = b * a := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => show Int.ofNat (m * n) = Int.ofNat (n * m); rw [Nat.mul_comm]
    | negSucc n => show Int.negOfNat (m * n.succ) = Int.negOfNat (n.succ * m); rw [Nat.mul_comm]
  | negSucc m => cases b with
    | ofNat n => show Int.negOfNat (m.succ * n) = Int.negOfNat (n * m.succ); rw [Nat.mul_comm]
    | negSucc n => show Int.ofNat (m.succ * n.succ) = Int.ofNat (n.succ * m.succ); rw [Nat.mul_comm]
theorem t055 (a : Int) : 0 * a = 0 := by
  cases a with
  | ofNat n => show Int.ofNat (0 * n) = Int.ofNat 0; rw [Nat.zero_mul]
  | negSucc n => show Int.negOfNat (0 * n.succ) = (0:Int); rw [Nat.zero_mul]; rfl
theorem t022 (a : Int) : a * 0 = 0 := by rw [t014]; exact t055 a
theorem t020 (a : Int) : a * 1 = a := by
  cases a with
  | ofNat n => show Int.ofNat (n * 1) = Int.ofNat n; rw [Nat.mul_one]
  | negSucc n => show Int.negOfNat (n.succ * 1) = Int.negSucc n; rw [Nat.mul_one]; rfl
theorem t037 (a : Int) : 1 * a = a := by rw [t014]; exact t020 a
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
theorem t018 (a b : Int) : a * (-b) = -(a * b) := by rw [t014 a (-b), t027, t014]
theorem t024 (c m n : Nat) (h : n ≤ m) : c * (m - n) = c * m - c * n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [t012 n d, Nat.left_distrib c n d, t012 (c*n) (c*d)]
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
theorem t034 (p q : Nat) : Int.ofNat p * Int.ofNat q = Int.ofNat (p*q) := rfl
theorem t033 (p q : Nat) : Int.ofNat p * Int.negSucc q = -(Int.ofNat (p*(q+1))) := by
  rw [show Int.negSucc q = -(Int.ofNat (q+1)) from rfl, t018]; rfl
theorem t031 (a b : Nat) : Int.ofNat a + -(Int.ofNat b) = Int.subNatNat a b := by
  cases b with
  | zero => show Int.ofNat a + 0 = Int.subNatNat a 0; rw [Int.add_zero, t043 (Nat.zero_le a), Nat.sub_zero]
  | succ k => show Int.ofNat a + Int.negSucc k = Int.subNatNat a (k+1); rfl
theorem t029 (a b : Nat) : -(Int.ofNat a) + Int.ofNat b = Int.subNatNat b a := by
  rw [t004, t031]
theorem t028 (a b : Nat) :
    -(Int.ofNat a) + -(Int.ofNat b) = -(Int.ofNat (a + b)) := by
  rw [← t025]; rfl
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
theorem t015 (a b c : Int) : a * (b + c) = a * b + a * c := by
  cases a with
  | ofNat p => exact t032 p b c
  | negSucc p =>
    show (-(Int.ofNat (p+1))) * (b + c) = (-(Int.ofNat (p+1))) * b + (-(Int.ofNat (p+1))) * c
    rw [t027, t027, t027, t032 (p+1) b c, t025]
theorem t007 (a b c : Int) : (a + b) * c = a * c + b * c := by
  rw [t014 (a+b) c, t015, t014 c a, t014 c b]
theorem t023 (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ d ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.left_distrib, ih]
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
theorem t019 (a : Int) : a * (-1) = -a := by rw [t018, t020]

theorem t052 (a : Int) : a - 0 = a := by
  rw [Int.sub_eq_add_neg]; show a + (-0) = a; rw [show (-0:Int) = 0 from rfl, Int.add_zero]
theorem t048 (a b : Int) : a - b + b = a := by
  rw [Int.sub_eq_add_neg, t005, t006, Int.add_zero]
theorem t013 (a b : Int) : a + b - b = a := by
  rw [Int.sub_eq_add_neg, t005, t008, Int.add_zero]
theorem t030 (a b : Int) : -(a - b) = b - a := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, t025, Int.neg_neg, t004]
theorem t021 (a b c : Int) : a * (b - c) = a * b - a * c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, t015, t018]
theorem t050 (a b c : Int) : (a - b) * c = a * c - b * c := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, t007, t027]
theorem t051 (a b c : Int) : a - b - c = a - (b + c) := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg, t005, t025]

theorem t053 (a : Int) : 2 * a = a + a := by
  rw [show (2:Int) = 1 + 1 from rfl, t007, t037]
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

end Foam
