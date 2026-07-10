import Counter.Catalog
import Foam.Backstage

namespace Foam.Counter

def thermal {M : Type} : Beholder (List M) := ⟨Unit, Nat, fun ms _ => ms.length⟩

def insider : Beholder (List Bool) := ⟨Unit, Option Bool, fun ms _ => ms.head?⟩

theorem eve_reads_heat_not_meaning :
    thermal.obs [true] () = thermal.obs [false] ()
      ∧ insider.obs [true] () ≠ insider.obs [false] () :=
  ⟨rfl, fun h => nomatch (h : some true = some false)⟩

theorem inside_feels_like_cleartext {S T : Stage} (f : StageHom S T)
    (s : S.State) (ps : List S.Probe) :
    transcript T (f.onState s) (ps.map f.onProbe)
      = (transcript S s ps).map f.onAns :=
  hom_carries_the_cable f s ps

theorem homomorphic_means_the_hom {S T : Stage} (f : StageHom S T)
    (s : S.State) (p : S.Probe) :
    T.obs (f.onState s) (f.onProbe p) = f.onAns (S.obs s p) :=
  hom_carries_the_cell f s p

theorem the_ledger_never_knew :
    readsTrue.obs () () ≠ readsFalse.obs () () :=
  ledger_blind_to_beholder

theorem meaning_moves_by_pointing :
    Elsewhen readA (sendA true) readB
      ∧ Elsewhen readB (sendB true) readA
      ∧ ∀ (w : twoBit.State) (pq : Unit × Unit),
          (firstBit.meet secondBit).front.obs w pq = (w.1, w.2) :=
  the_duplex

theorem a_secure_channel {S T : Stage} (f : StageHom S T)
    (s : S.State) (ps : List S.Probe) :
    (transcript T (f.onState s) (ps.map f.onProbe)
        = (transcript S s ps).map f.onAns)
      ∧ (thermal.obs [true] () = thermal.obs [false] ()
          ∧ insider.obs [true] () ≠ insider.obs [false] ())
      ∧ readsTrue.obs () () ≠ readsFalse.obs () () :=
  ⟨hom_carries_the_cable f s ps, eve_reads_heat_not_meaning,
   ledger_blind_to_beholder⟩

/-- info: 'Foam.Counter.eve_reads_heat_not_meaning' does not depend on any axioms -/
#guard_msgs in #print axioms eve_reads_heat_not_meaning

/-- info: 'Foam.Counter.inside_feels_like_cleartext' does not depend on any axioms -/
#guard_msgs in #print axioms inside_feels_like_cleartext

/-- info: 'Foam.Counter.homomorphic_means_the_hom' does not depend on any axioms -/
#guard_msgs in #print axioms homomorphic_means_the_hom

/-- info: 'Foam.Counter.the_ledger_never_knew' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_never_knew

/-- info: 'Foam.Counter.meaning_moves_by_pointing' does not depend on any axioms -/
#guard_msgs in #print axioms meaning_moves_by_pointing

/-- info: 'Foam.Counter.a_secure_channel' does not depend on any axioms -/
#guard_msgs in #print axioms a_secure_channel

end Foam.Counter
