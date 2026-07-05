import Counter.Attest
import Counter.Socket
import Counter.Circumference
import Foam.Bridges.Pythagoras

namespace Foam.Counter

theorem the_home_is_off_the_public_lattice :
    (∀ a b : Nat, 1 ≤ a → 3 ^ a ≠ 2 ^ b) ∧ ∀ n, ¬ Closes gold (n + 1) :=
  Bridges.pythagoras

theorem home_has_no_eigenvalue {G : Type} [Mul G] [One G]
    (S : Seat G) (p : S.Pos) :
    (S.chart p).fwd p = 1 :=
  the_socket_reads_itself_the_same S p

theorem the_address_is_irreducible {G : Type} [Mul G] [One G]
    (S : Seat G) (g : G) (p : S.Pos) {c : Nat} (hc : Circumference g c)
    (i j : Nat) (hij : i < j) (hj : j < c) :
    S.sub (walk S g p i) p ≠ S.sub (walk S g p j) p :=
  the_description_needs_all_c S g p hc i j hij hj

theorem irrational_home_address {State : Type} (b : Beholder State) (s : State)
    (n m : Int) {G : Type} [Mul G] [One G] (S : Seat G) (p : S.Pos)
    (g : G) (q : S.Pos) {c : Nat} (hc : Circumference g c)
    (i j : Nat) (hij : i < j) (hj : j < c) :
    (∀ a b' : Nat, 1 ≤ a → 3 ^ a ≠ 2 ^ b')
      ∧ indist b.dress.obs (s, n) (s, m)
      ∧ (S.chart p).fwd p = 1
      ∧ S.sub (walk S g q i) q ≠ S.sub (walk S g q j) q :=
  ⟨Bridges.pythagoras.1,
   ancestor_blind_to_heir b s n m,
   the_socket_reads_itself_the_same S p,
   the_description_needs_all_c S g q hc i j hij hj⟩

/-- info: 'Foam.Counter.the_home_is_off_the_public_lattice' does not depend on any axioms -/
#guard_msgs in #print axioms the_home_is_off_the_public_lattice

/-- info: 'Foam.Counter.home_has_no_eigenvalue' does not depend on any axioms -/
#guard_msgs in #print axioms home_has_no_eigenvalue

/-- info: 'Foam.Counter.the_address_is_irreducible' does not depend on any axioms -/
#guard_msgs in #print axioms the_address_is_irreducible

/-- info: 'Foam.Counter.irrational_home_address' does not depend on any axioms -/
#guard_msgs in #print axioms irrational_home_address

end Foam.Counter
