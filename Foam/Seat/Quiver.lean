namespace Foam

abbrev Quiver (Handle : Type) := List (Handle × Handle)

inductive Path {Handle : Type} (q : Quiver Handle) : Handle → Handle → Type where
  | nil  {a : Handle} : Path q a a
  | cons {a b c : Handle} : ((a, b) ∈ q) → Path q b c → Path q a c

def Path.comp {Handle : Type} {q : Quiver Handle} :
    {a b c : Handle} → Path q a b → Path q b c → Path q a c
  | _, _, _, Path.nil,      p => p
  | _, _, _, Path.cons e r, p => Path.cons e (r.comp p)

theorem Path.nil_comp {Handle : Type} {q : Quiver Handle} {a b : Handle}
    (p : Path q a b) : Path.nil.comp p = p := rfl

theorem Path.comp_nil {Handle : Type} {q : Quiver Handle} {a b : Handle}
    (p : Path q a b) : p.comp Path.nil = p := by
  induction p with
  | nil => rfl
  | cons e r ih => exact congrArg (Path.cons e) ih

theorem Path.comp_assoc {Handle : Type} {q : Quiver Handle} :
    {a b c d : Handle} → (p : Path q a b) → (r : Path q b c) → (s : Path q c d) →
    (p.comp r).comp s = p.comp (r.comp s)
  | _, _, _, _, Path.nil,      _, _ => rfl
  | _, _, _, _, Path.cons e p, r, s => congrArg (Path.cons e) (Path.comp_assoc p r s)

def Path.edges {Handle : Type} {q : Quiver Handle} :
    {a b : Handle} → Path q a b → List (Handle × Handle)
  | _, _, Path.nil                 => []
  | _, _, @Path.cons _ _ a b _ _ r => (a, b) :: r.edges

theorem Path.edges_comp {Handle : Type} {q : Quiver Handle} :
    {a b c : Handle} → (p : Path q a b) → (r : Path q b c) →
    (p.comp r).edges = p.edges ++ r.edges
  | _, _, _, Path.nil,                 _ => rfl
  | _, _, _, @Path.cons _ _ a b _ _ p, r =>
      congrArg ((a, b) :: ·) (Path.edges_comp p r)

def Quiver.reverse {Handle : Type} (q : Quiver Handle) : Quiver Handle :=
  q.map (fun e => (e.2, e.1))

theorem mem_reverse {Handle : Type} {q : Quiver Handle} {a b : Handle}
    (h : (a, b) ∈ q) : (b, a) ∈ q.reverse := by
  induction h with
  | head as     => exact List.Mem.head _
  | tail e _ ih => exact List.Mem.tail _ ih

def Path.reverse {Handle : Type} {q : Quiver Handle} :
    {a b : Handle} → Path q a b → Path q.reverse b a
  | _, _, Path.nil      => Path.nil
  | _, _, Path.cons e r => r.reverse.comp (Path.cons (mem_reverse e) Path.nil)

theorem Path.reverse_nil {Handle : Type} {q : Quiver Handle} {a : Handle} :
    (Path.nil : Path q a a).reverse = Path.nil := rfl

theorem Path.reverse_comp {Handle : Type} {q : Quiver Handle} :
    {a b c : Handle} → (p : Path q a b) → (r : Path q b c) →
    (p.comp r).reverse = r.reverse.comp p.reverse
  | _, _, _, Path.nil,      r => (Path.comp_nil r.reverse).symm
  | _, _, _, Path.cons e p, r => by
      have ih := Path.reverse_comp p r
      show (p.comp r).reverse.comp (Path.cons (mem_reverse e) Path.nil)
         = r.reverse.comp (p.reverse.comp (Path.cons (mem_reverse e) Path.nil))
      rw [ih]
      exact Path.comp_assoc r.reverse p.reverse _

theorem Quiver.reverse_reverse {Handle : Type} :
    ∀ (q : Quiver Handle), q.reverse.reverse = q
  | []      => rfl
  | e :: es => congrArg (e :: ·) (Quiver.reverse_reverse es)

/-- info: 'Foam.Path.nil_comp' does not depend on any axioms -/
#guard_msgs in #print axioms Path.nil_comp

/-- info: 'Foam.Path.comp_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Path.comp_nil

/-- info: 'Foam.Path.comp_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms Path.comp_assoc

/-- info: 'Foam.Path.edges_comp' does not depend on any axioms -/
#guard_msgs in #print axioms Path.edges_comp

/-- info: 'Foam.mem_reverse' does not depend on any axioms -/
#guard_msgs in #print axioms mem_reverse

/-- info: 'Foam.Path.reverse_nil' does not depend on any axioms -/
#guard_msgs in #print axioms Path.reverse_nil

/-- info: 'Foam.Path.reverse_comp' does not depend on any axioms -/
#guard_msgs in #print axioms Path.reverse_comp

/-- info: 'Foam.Quiver.reverse_reverse' does not depend on any axioms -/
#guard_msgs in #print axioms Quiver.reverse_reverse

end Foam