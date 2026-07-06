import Sim.Model

namespace Foam.Sim

inductive J where
  | null : J
  | num : Int → J
  | str : String → J
  | arr : List J → J
  | obj : List (String × J) → J
  deriving Repr

def escape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c = '"' then "\\\""
            else if c = '\\' then "\\\\"
            else if c = '\n' then "\\n"
            else String.singleton c)) ""

partial def J.render : J → String
  | .null => "null"
  | .num i => toString i
  | .str s => "\"" ++ escape s ++ "\""
  | .arr xs => "[" ++ String.intercalate "," (xs.map J.render) ++ "]"
  | .obj fs =>
    "{" ++ String.intercalate ","
      (fs.map (fun f => "\"" ++ escape f.1 ++ "\":" ++ f.2.render)) ++ "}"

def encNat (n : Nat) : J := .num (Int.ofNat n)

def decNat : J → Option Nat
  | .num (.ofNat k) => some k
  | .num (.negSucc _) => none
  | .null | .str _ | .arr _ | .obj _ => none

theorem nat_roundtrip (n : Nat) : decNat (encNat n) = some n := rfl

def decStr : J → Option String
  | .str s => some s
  | .null | .num _ | .arr _ | .obj _ => none

def decParent : J → Option (Option Nat)
  | .null => some none
  | .num (.ofNat k) => some (some k)
  | .num (.negSucc _) => none
  | .str _ | .arr _ | .obj _ => none

def encActor (a : Actor) : J :=
  .obj [("id", encNat a.id), ("name", .str a.name),
        ("parent", match a.parent with | none => .null | some p => encNat p)]

def decActor3 (j1 j2 j3 : J) : Option Actor :=
  match decNat j1 with
  | none => none
  | some i =>
    match decStr j2 with
    | none => none
    | some n =>
      match decParent j3 with
      | none => none
      | some p => some ⟨i, n, p⟩

def decActor : J → Option Actor
  | .obj ((_, j1) :: (_, j2) :: (_, j3) :: []) => decActor3 j1 j2 j3
  | .obj [] | .obj (_ :: []) | .obj (_ :: _ :: []) => none
  | .obj (_ :: _ :: _ :: _ :: _) => none
  | .null | .num _ | .str _ | .arr _ => none

theorem actor_roundtrip (a : Actor) : decActor (encActor a) = some a := by
  cases a with
  | mk i n p => cases p <;> rfl

def encAct (a : Act) : J :=
  .obj [("id", encNat a.id), ("actor", encNat a.actor),
        ("position", encNat a.position), ("verb", .str a.verb),
        ("src", .str a.src), ("dst", .str a.dst)]

def decAct6 (j1 j2 j3 j4 j5 j6 : J) : Option Act :=
  match decNat j1 with
  | none => none
  | some i =>
    match decNat j2 with
    | none => none
    | some ac =>
      match decNat j3 with
      | none => none
      | some pos =>
        match decStr j4 with
        | none => none
        | some v =>
          match decStr j5 with
          | none => none
          | some s =>
            match decStr j6 with
            | none => none
            | some d => some ⟨i, ac, pos, v, s, d⟩

def decAct : J → Option Act
  | .obj ((_, j1) :: (_, j2) :: (_, j3) :: (_, j4) :: (_, j5) :: (_, j6) :: []) =>
    decAct6 j1 j2 j3 j4 j5 j6
  | .obj [] | .obj (_ :: []) | .obj (_ :: _ :: []) => none
  | .obj (_ :: _ :: _ :: []) | .obj (_ :: _ :: _ :: _ :: []) => none
  | .obj (_ :: _ :: _ :: _ :: _ :: []) => none
  | .obj (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _) => none
  | .null | .num _ | .str _ | .arr _ => none

theorem act_roundtrip (a : Act) : decAct (encAct a) = some a := by
  cases a
  rfl

def decAll {α : Type} (dec : J → Option α) : List J → Option (List α)
  | [] => some []
  | x :: xs =>
    match dec x with
    | none => none
    | some a =>
      match decAll dec xs with
      | none => none
      | some rest => some (a :: rest)

theorem decAll_enc {α : Type} (enc : α → J) (dec : J → Option α)
    (h : ∀ a, dec (enc a) = some a) :
    ∀ xs : List α, decAll dec (xs.map enc) = some xs
  | [] => rfl
  | x :: xs => by
    show decAll dec (enc x :: xs.map enc) = some (x :: xs)
    unfold decAll
    rw [h x, decAll_enc enc dec h xs]

def encModel (m : Model) : J :=
  .obj [("name", .str m.name),
        ("actors", .arr (m.actors.map encActor)),
        ("acts", .arr (m.acts.map encAct))]

def obind {α β : Type} (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none => none
  | some a => f a

def decActors : J → Option (List Actor)
  | .arr xs => decAll decActor xs
  | .null | .num _ | .str _ | .obj _ => none

def decActs : J → Option (List Act)
  | .arr xs => decAll decAct xs
  | .null | .num _ | .str _ | .obj _ => none

def decModel3 (j1 j2 j3 : J) : Option Model :=
  obind (decStr j1) fun n =>
  obind (decActors j2) fun actors =>
  obind (decActs j3) fun acts => some ⟨n, actors, acts⟩

def decModel : J → Option Model
  | .obj ((_, j1) :: (_, j2) :: (_, j3) :: []) => decModel3 j1 j2 j3
  | .obj [] | .obj (_ :: []) | .obj (_ :: _ :: []) => none
  | .obj (_ :: _ :: _ :: _ :: _) => none
  | .null | .num _ | .str _ | .arr _ => none

theorem model_roundtrip (m : Model) : decModel (encModel m) = some m := by
  cases m with
  | mk n actors acts =>
    have h1 : decActors (.arr (actors.map encActor)) = some actors :=
      decAll_enc encActor decActor actor_roundtrip actors
    have h2 : decActs (.arr (acts.map encAct)) = some acts :=
      decAll_enc encAct decAct act_roundtrip acts
    show obind (decActors (.arr (actors.map encActor))) (fun as =>
          obind (decActs (.arr (acts.map encAct))) (fun xs =>
            some (Model.mk n as xs))) = some (Model.mk n actors acts)
    rw [h1, h2]
    rfl

/-- info: 'Foam.Sim.nat_roundtrip' does not depend on any axioms -/
#guard_msgs in #print axioms nat_roundtrip

/-- info: 'Foam.Sim.actor_roundtrip' does not depend on any axioms -/
#guard_msgs in #print axioms actor_roundtrip

/-- info: 'Foam.Sim.act_roundtrip' does not depend on any axioms -/
#guard_msgs in #print axioms act_roundtrip

/-- info: 'Foam.Sim.decAll_enc' does not depend on any axioms -/
#guard_msgs in #print axioms decAll_enc

/-- info: 'Foam.Sim.model_roundtrip' does not depend on any axioms -/
#guard_msgs in #print axioms model_roundtrip

end Foam.Sim
