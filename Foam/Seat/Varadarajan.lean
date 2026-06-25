import Foam.Seat.Frame
import Foam.Seat.Characters

namespace Foam

theorem coord_is_character : Char.chi = Rot.amp := rfl

theorem coord_unitary_rep :
    (∀ a b, Char.chi (a * b) = GInt.mul (Char.chi a) (Char.chi b))
      ∧ (∀ a, (Char.chi a).normSq = 1) :=
  ⟨Char.chi_hom, Char.chi_unit⟩

theorem characters_orthonormal :
    (Char.inner Char.count Char.count = ⟨4, 0⟩
      ∧ Char.inner Char.alt Char.alt = ⟨4, 0⟩
      ∧ Char.inner Char.chi Char.chi = ⟨4, 0⟩
      ∧ Char.inner Char.chiBar Char.chiBar = ⟨4, 0⟩)
    ∧ (Char.inner Char.count Char.alt = GInt.zero
      ∧ Char.inner Char.count Char.chi = GInt.zero
      ∧ Char.inner Char.count Char.chiBar = GInt.zero
      ∧ Char.inner Char.alt Char.chi = GInt.zero
      ∧ Char.inner Char.alt Char.chiBar = GInt.zero
      ∧ Char.inner Char.chi Char.chiBar = GInt.zero) :=
  ⟨⟨Char.count_norm, Char.alt_norm, Char.chi_norm, Char.chiBar_norm⟩,
   ⟨Char.count_alt_orth, Char.count_chi_orth, Char.count_chiBar_orth,
    Char.alt_chi_orth, Char.alt_chiBar_orth, Char.chi_chiBar_orth⟩⟩

theorem observables_reconstruct (n0 n1 n2 n3 : Int) :
    (Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3)
        + Char.twice (Char.readRe n0 n1 n2 n3) = Char.twice (Char.twice n0) ∧
    (Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3)
        + Char.twice (Char.readIm n0 n1 n2 n3) = Char.twice (Char.twice n1) ∧
    (Char.readBal n0 n1 n2 n3 + Char.readAlt n0 n1 n2 n3)
        + -Char.twice (Char.readRe n0 n1 n2 n3) = Char.twice (Char.twice n2) ∧
    (Char.readBal n0 n1 n2 n3 + -Char.readAlt n0 n1 n2 n3)
        + -Char.twice (Char.readIm n0 n1 n2 n3) = Char.twice (Char.twice n3) :=
  Char.lossless n0 n1 n2 n3

theorem varadarajan :
    (Char.chi = Rot.amp)
      ∧ ((∀ a b, Char.chi (a * b) = GInt.mul (Char.chi a) (Char.chi b))
          ∧ (∀ a, (Char.chi a).normSq = 1))
      ∧ ((Char.inner Char.count Char.count = ⟨4, 0⟩
            ∧ Char.inner Char.alt Char.alt = ⟨4, 0⟩
            ∧ Char.inner Char.chi Char.chi = ⟨4, 0⟩
            ∧ Char.inner Char.chiBar Char.chiBar = ⟨4, 0⟩)
          ∧ (Char.inner Char.count Char.alt = GInt.zero
            ∧ Char.inner Char.count Char.chi = GInt.zero
            ∧ Char.inner Char.count Char.chiBar = GInt.zero
            ∧ Char.inner Char.alt Char.chi = GInt.zero
            ∧ Char.inner Char.alt Char.chiBar = GInt.zero
            ∧ Char.inner Char.chi Char.chiBar = GInt.zero))
      ∧ (OpenChannels 3 ∧ ¬ OpenChannels 4) :=
  ⟨coord_is_character, coord_unitary_rep, characters_orthonormal, dimension_caps_at_three⟩

/-- info: 'Foam.coord_is_character' does not depend on any axioms -/
#guard_msgs in #print axioms coord_is_character

/-- info: 'Foam.coord_unitary_rep' does not depend on any axioms -/
#guard_msgs in #print axioms coord_unitary_rep

/-- info: 'Foam.characters_orthonormal' does not depend on any axioms -/
#guard_msgs in #print axioms characters_orthonormal

/-- info: 'Foam.observables_reconstruct' does not depend on any axioms -/
#guard_msgs in #print axioms observables_reconstruct

/-- info: 'Foam.varadarajan' does not depend on any axioms -/
#guard_msgs in #print axioms varadarajan

end Foam
