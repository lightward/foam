import Foam.Engine.Stream

namespace Foam

def d017 {B : Type} : List (List B) → List B
  | []      => []
  | s :: ss => s ++ d017 ss

theorem t115 {B : Type} :
    ∀ (xs ys : List (List B)), d017 (xs ++ ys) = d017 xs ++ d017 ys
  | [],      _  => rfl
  | s :: xs, ys =>
      (congrArg (s ++ ·) (t115 xs ys)).trans
        (t070 s (d017 xs) (d017 ys)).symm

section Codec
variable {B D : Type} (knows : D → List B → Bool) (learn : D → List B → D)

def d013 (s : D × List B) (b : B) : (D × List B) × List (List B) :=
  match knows s.1 (s.2 ++ [b]) with
  | true  => ((s.1, s.2 ++ [b]), [])
  | false => ((learn s.1 (s.2 ++ [b]), []), [s.2 ++ [b]])

def d012 (s : D × List B) : List (List B) :=
  match s.2 with
  | []     => []
  | a :: l => [a :: l]

def d088 : List (List B) → List B := d017

def d189 (d₀ : D) (x : List B) : List (List B) :=
  d150 (d013 knows learn) d012 (d₀, []) x

theorem t116 (s : D × List B) : d017 (d012 s) = s.2 := by
  obtain ⟨d, cur⟩ := s
  cases cur with
  | nil      => rfl
  | cons a l => exact t071 (a :: l)

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

theorem t385 (d₀ : D) (x : List B) :
    d088 (d189 knows learn d₀ x) = x := by
  show d017 (d026 (d013 knows learn) (d₀, []) x
        ++ d012 (d099 (d013 knows learn) (d₀, []) x)) = x
  rw [t115, t116]
  exact (t166 knows learn (d₀, []) x).trans rfl

end Codec

/-- info: 'Foam.t115' does not depend on any axioms -/
#guard_msgs in #print axioms t115

/-- info: 'Foam.t116' does not depend on any axioms -/
#guard_msgs in #print axioms t116

/-- info: 'Foam.t166' does not depend on any axioms -/
#guard_msgs in #print axioms t166

/-- info: 'Foam.t385' does not depend on any axioms -/
#guard_msgs in #print axioms t385

end Foam
