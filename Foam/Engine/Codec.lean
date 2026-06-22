import Foam.Engine.Stream

namespace Foam

def joinB {B : Type} : List (List B) → List B
  | []      => []
  | s :: ss => s ++ joinB ss

theorem joinB_append {B : Type} :
    ∀ (xs ys : List (List B)), joinB (xs ++ ys) = joinB xs ++ joinB ys
  | [],      _  => rfl
  | s :: xs, ys =>
      (congrArg (s ++ ·) (joinB_append xs ys)).trans
        (appendAssoc s (joinB xs) (joinB ys)).symm

section Codec
variable {B D : Type} (knows : D → List B → Bool) (learn : D → List B → D)

def encStep (s : D × List B) (b : B) : (D × List B) × List (List B) :=
  match knows s.1 (s.2 ++ [b]) with
  | true  => ((s.1, s.2 ++ [b]), [])
  | false => ((learn s.1 (s.2 ++ [b]), []), [s.2 ++ [b]])

def encFlush (s : D × List B) : List (List B) :=
  match s.2 with
  | []     => []
  | a :: l => [a :: l]

def decode : List (List B) → List B := joinB

def encode (d₀ : D) (x : List B) : List (List B) :=
  output (encStep knows learn) encFlush (d₀, []) x

theorem joinB_encFlush (s : D × List B) : joinB (encFlush s) = s.2 := by
  obtain ⟨d, cur⟩ := s
  cases cur with
  | nil      => rfl
  | cons a l => exact appendNil (a :: l)

theorem encode_covers :
    ∀ (s : D × List B) (ys : List B),
    joinB (runEmit (encStep knows learn) s ys)
        ++ (runState (encStep knows learn) s ys).2
      = s.2 ++ ys
  | s, []      => (appendNil s.2).symm
  | s, b :: bs => by
      cases hk : knows s.1 (s.2 ++ [b]) with
      | true =>
        have e : encStep knows learn s b = ((s.1, s.2 ++ [b]), []) := by
          unfold encStep; rw [hk]
        show joinB ((encStep knows learn s b).2
                ++ runEmit (encStep knows learn) (encStep knows learn s b).1 bs)
              ++ (runState (encStep knows learn) (encStep knows learn s b).1 bs).2
            = s.2 ++ (b :: bs)
        rw [e]
        show joinB (runEmit (encStep knows learn) (s.1, s.2 ++ [b]) bs)
              ++ (runState (encStep knows learn) (s.1, s.2 ++ [b]) bs).2
            = s.2 ++ (b :: bs)
        rw [encode_covers (s.1, s.2 ++ [b]) bs]
        show (s.2 ++ [b]) ++ bs = s.2 ++ (b :: bs)
        exact appendAssoc s.2 [b] bs
      | false =>
        have e : encStep knows learn s b
            = ((learn s.1 (s.2 ++ [b]), []), [s.2 ++ [b]]) := by
          unfold encStep; rw [hk]
        show joinB ((encStep knows learn s b).2
                ++ runEmit (encStep knows learn) (encStep knows learn s b).1 bs)
              ++ (runState (encStep knows learn) (encStep knows learn s b).1 bs).2
            = s.2 ++ (b :: bs)
        rw [e]
        show (s.2 ++ [b])
              ++ joinB (runEmit (encStep knows learn) (learn s.1 (s.2 ++ [b]), []) bs)
              ++ (runState (encStep knows learn) (learn s.1 (s.2 ++ [b]), []) bs).2
            = s.2 ++ (b :: bs)
        rw [appendAssoc (s.2 ++ [b]), encode_covers (learn s.1 (s.2 ++ [b]), []) bs]
        show (s.2 ++ [b]) ++ bs = s.2 ++ (b :: bs)
        exact appendAssoc s.2 [b] bs

theorem lossless_codec (d₀ : D) (x : List B) :
    decode (encode knows learn d₀ x) = x := by
  show joinB (runEmit (encStep knows learn) (d₀, []) x
        ++ encFlush (runState (encStep knows learn) (d₀, []) x)) = x
  rw [joinB_append, joinB_encFlush]
  exact (encode_covers knows learn (d₀, []) x).trans rfl

end Codec

/-- info: 'Foam.joinB_append' does not depend on any axioms -/
#guard_msgs in #print axioms joinB_append

/-- info: 'Foam.joinB_encFlush' does not depend on any axioms -/
#guard_msgs in #print axioms joinB_encFlush

/-- info: 'Foam.encode_covers' does not depend on any axioms -/
#guard_msgs in #print axioms encode_covers

/-- info: 'Foam.lossless_codec' does not depend on any axioms -/
#guard_msgs in #print axioms lossless_codec

end Foam
