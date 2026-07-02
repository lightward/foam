import Counter.Legible

namespace Foam.Counter

theorem identity_is_free {H : Type} (q : Quiver H) (a : H) :
    Nonempty (Path q a a) :=
  ⟨Path.nil⟩

theorem composition_is_free {H : Type} {q : Quiver H} {a b c : H}
    (p : Path q a b) (r : Path q b c) :
    (p.comp r).edges = p.edges ++ r.edges :=
  Path.edges_comp p r

theorem distinction_is_priced {H : Type} (q : Quiver H) (e : H × H) :
    (q.deposit e).length = q.length + 1 :=
  deposit_monotone q e

theorem no_collapse_inside {A : Type} [DecidableEq A] (a b : A) (hab : a ≠ b) :
    (∀ s, Ledger.freq [a, b] s = Ledger.freq [b, a] s)
      ∧ Ledger.order [a, b] ≠ Ledger.order [b, a] :=
  ⟨(Ledger.order_finer a b hab).2.1, (Ledger.order_finer a b hab).2.2⟩

theorem the_categorical_contract {H : Type} (q : Quiver H) (a : H) (e : H × H)
    {A : Type} [DecidableEq A] (x y : A) (hxy : x ≠ y) :
    Nonempty (Path q a a)
      ∧ (q.deposit e).length = q.length + 1
      ∧ (∀ s, Ledger.freq [x, y] s = Ledger.freq [y, x] s)
      ∧ Ledger.order [x, y] ≠ Ledger.order [y, x] :=
  ⟨⟨Path.nil⟩, deposit_monotone q e,
   (Ledger.order_finer x y hxy).2.1, (Ledger.order_finer x y hxy).2.2⟩

/-- info: 'Foam.Counter.identity_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms identity_is_free

/-- info: 'Foam.Counter.composition_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms composition_is_free

/-- info: 'Foam.Counter.distinction_is_priced' does not depend on any axioms -/
#guard_msgs in #print axioms distinction_is_priced

/-- info: 'Foam.Counter.no_collapse_inside' does not depend on any axioms -/
#guard_msgs in #print axioms no_collapse_inside

/-- info: 'Foam.Counter.the_categorical_contract' does not depend on any axioms -/
#guard_msgs in #print axioms the_categorical_contract

end Foam.Counter
