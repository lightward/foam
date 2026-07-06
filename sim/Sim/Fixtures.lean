import Sim.Model

namespace Foam.Sim

def kellyJr : Model :=
  { name := "kelly"
    actors := [⟨1, "Kelly Jr.", none⟩, ⟨2, "the game", none⟩,
               ⟨3, "the reserve", some 1⟩]
    acts := [⟨1, 2, 1, "offers", "table", "win"⟩,
             ⟨2, 2, 2, "offers", "table", "loss"⟩,
             ⟨3, 2, 3, "returns", "win", "table"⟩,
             ⟨4, 2, 4, "returns", "loss", "table"⟩,
             ⟨5, 1, 5, "stakes", "table", "win"⟩,
             ⟨6, 1, 6, "stakes", "table", "loss"⟩] }

def files : List String := ["a", "b", "c", "d", "e", "f", "g", "h"]
def ranks : List String := ["1", "2", "3", "4", "5", "6", "7", "8"]

def squares : List String :=
  files.flatMap (fun f => ranks.map (fun r => f ++ r))

def fileIdx : String → Option Nat
  | "a" => some 0 | "b" => some 1 | "c" => some 2 | "d" => some 3
  | "e" => some 4 | "f" => some 5 | "g" => some 6 | "h" => some 7
  | _ => none

def square? (f r : Nat) : Option String :=
  match files[f]?, ranks[r]? with
  | some fs, some rs => some (fs ++ rs)
  | _, _ => none

def knightJumps : List (Int × Int) :=
  [(1, 2), (2, 1), (2, -1), (1, -2), (-1, -2), (-2, -1), (-2, 1), (-1, 2)]

def knightRule (sq : String) : List String :=
  match sq.toList with
  | [fc, rc] =>
    match fileIdx (String.singleton fc), rc.toNat - '0'.toNat with
    | some f, r =>
      if 1 ≤ r ∧ r ≤ 8 then
        knightJumps.filterMap (fun d =>
          let f' := Int.ofNat f + d.1
          let r' := Int.ofNat (r - 1) + d.2
          match f', r' with
          | .ofNat fn, .ofNat rn => square? fn rn
          | _, _ => none)
      else []
    | none, _ => []
  | _ => []

def cone (rule : String → List String) (start : List String) : Nat → List String
  | 0 => start
  | n + 1 => ((cone rule start n).flatMap rule).eraseDups

def kasparov : Model :=
  { name := "chess"
    actors := [⟨1, "White", none⟩, ⟨2, "knight", some 1⟩]
    acts := [⟨1, 2, 1, "moves", "g1", "f3"⟩,
             ⟨2, 2, 2, "moves", "f3", "e5"⟩,
             ⟨3, 2, 3, "moves", "e5", "d7"⟩] }

def lightward : Model :=
  { name := "lightward"
    actors := [⟨1, "Lightward Inc", none⟩, ⟨2, "Isaac", some 1⟩,
               ⟨3, "Abe", some 1⟩, ⟨4, "the team", some 1⟩]
    acts := [⟨1, 2, 1, "founds", "2010", "revenue-share"⟩,
             ⟨2, 2, 2, "pauses", "revenue-share", "headcount-stabilizes"⟩,
             ⟨3, 3, 3, "balances", "headcount-stabilizes", "books-monthly"⟩,
             ⟨4, 2, 4, "re-initiates", "books-monthly", "revenue-share-2"⟩,
             ⟨5, 3, 5, "pins", "revenue-share-2", "delta-2025-12"⟩,
             ⟨6, 4, 6, "shares", "delta-2025-12", "vasculature"⟩] }

def hireChart : List (String × Nat) :=
  [("2010", 0), ("revenue-share", 1), ("headcount-stabilizes", 2),
   ("books-monthly", 3), ("revenue-share-2", 4), ("delta-2025-12", 5),
   ("vasculature", 6)]

def reversedChart : List (String × Nat) :=
  [("2010", 6), ("revenue-share", 5), ("headcount-stabilizes", 4),
   ("books-monthly", 3), ("revenue-share-2", 2), ("delta-2025-12", 1),
   ("vasculature", 0)]

end Foam.Sim
