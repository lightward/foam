import Face
open Room Face

-- the chinese room, played at the air gap: boxes you can only interview. `ask` a word and hear the
-- conduct; `widen` to see the state one seat wider (it ends the box: you have left your seat);
-- `alike a b` to say two boxes are one box at this seat; `target` to see what you are to provoke.
-- the score is fuel: the cells you spent. every box is a machine of the house, run as itself.
-- run: lake env lean --run bin/play.lean   (or pipe lines in)

def ticks (w : List Nat) : List Unit := w.map fun _ => ()

structure Box where
  name : String
  target : String
  run : List Nat → String
  peek : List Nat → String

def boxes : List Box := [
  ⟨"the first box", "say 3 — then say it again for less",
    fun w => toString (behavior tally (ticks w)), fun w => let n : Nat := park tally (0 : Nat) (ticks w); s!"a counter at {n}"⟩,
  ⟨"the second box", "say true",
    fun w => toString (behavior flip (ticks w)), fun w => let b : Bool := park flip false (ticks w); s!"a bit at {b}"⟩,
  ⟨"the third box", "say true — is this the second box?",
    fun w => toString (behavior paceOne (ticks w)), fun w => let n : Nat := park paceOne (0 : Nat) (ticks w); s!"a counter at {n}, voiced odd"⟩,
  ⟨"the fourth box", "say 4 with three cells",
    fun w => toString (behavior (tape adder (0 : Nat) recordTheState readThrough) w),
    fun w => let d := park (tape adder (0 : Nat) recordTheState readThrough) (atTheDoor (0 : Nat) (0 : Nat)) w; s!"an adder at {(face d : Nat)} with a tape reading {(met d : Nat)}"⟩,
  ⟨"the fifth box", "say false, if any word can make it",
    fun w => toString (behavior restingCounter (ticks w)), fun w => let n : Nat := park restingCounter (0 : Nat) (ticks w); s!"a counter at {n}, muffled"⟩,
  ⟨"the sixth box", "say false, if any word can make it — is this the fifth box?",
    fun w => toString (behavior hollowShell (ticks w)), fun _ => "a shell: no state at all"⟩]

-- alike at the air gap, by the trunk's own receipts: the_pace_wears_the_tallys_voice carries the
-- third onto the second (the_pace_is_carried_onto_the_flip), the_flywheel_and_the_shell_sound_alike
-- the fifth onto the sixth. every other pair parts at some word.
def alikePairs : List (Nat × Nat) := [(2, 3), (5, 6)]

-- the seventh box: a foam generated from a dark seed. the seed is an index into `words 4`, an exact
-- enumeration (the_book_is_the_answer_space); it is read at the tamper surface (SEED, or the clock) and
-- by no seat after. the box is the pattern repeated forever; `hear 7 k` costs k cells; `make 7 b b …`
-- submits a pattern, and the win is alike at the air gap — the two streams agree — which for two
-- periods is decided at their product. the least pattern alike to the hidden one is its winding.
def patternAt (w : List Bool) (n : Nat) : Bool := (w[n % w.length]?).getD false
def stream (w : List Bool) (k : Nat) : List Bool := (List.range k).map (patternAt w)
def alikeAtTheGap (w w' : List Bool) : Bool :=
  w.length != 0 && w'.length != 0 && stream w (w.length * w'.length) == stream w' (w.length * w'.length)
def parseBits (ws : List String) : List Bool := ws.filterMap fun s => if s == "t" || s == "1" then some true else if s == "f" || s == "0" then some false else none

def parseNats (s : String) : List Nat :=
  (s.splitOn " ").filterMap fun t => t.trimAscii.toString.toNat?

partial def loop (hidden : List Bool) (fuel : Nat) : IO Unit := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then IO.println s!"the room is quiet. fuel spent: {fuel}"; return
  let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
  match ws with
  | ["boxes"] =>
      for (b, i) in boxes.zip (List.range boxes.length) do IO.println s!"  {i + 1}: {b.name} — provoke it to {b.target}"
      IO.println "  7: the seventh box — a pattern grown from a dark seed; hear it, then make a box alike to it at the air gap"
      loop hidden fuel
  | "ask" :: n :: w =>
      match n.toNat?, boxes[n.toNat?.getD 0 - 1]? with
      | some _, some b =>
          let word := parseNats (" ".intercalate w)
          IO.println s!"  {b.name} hears {word.length} cells and says: {b.run word}"
          loop hidden (fuel + word.length)
      | _, _ => IO.println "  ask <box> <cells…>"; loop hidden fuel
  | "widen" :: n :: w =>
      match boxes[n.toNat?.getD 0 - 1]? with
      | some b =>
          let word := parseNats (" ".intercalate w)
          IO.println s!"  one seat wider, {b.name} after that word is {b.peek word}. you have left your seat; the box is read."
          loop hidden (fuel + 1)
      | none => IO.println "  widen <box> <cells…>"; loop hidden fuel
  | ["alike", a, b] =>
      let p := (a.toNat?.getD 0, b.toNat?.getD 0)
      let q := (p.2, p.1)
      if p.1 == p.2 then IO.println "  a box is alike to itself at every seat: spacelike."
      else if alikePairs.contains p || alikePairs.contains q then
        IO.println "  yes: alike at the air gap — no interview parts them (the_audition_is_exact). at a wider seat they part: one has a state the other lacks."
      else IO.println "  no: some word parts them. find it."
      loop hidden fuel
  | ["hear", "7", k] =>
      let n := k.toNat?.getD 0
      IO.println s!"  the seventh box, heard for {n} cells: {stream hidden n}"
      loop hidden (fuel + n)
  | "make" :: "7" :: bits =>
      let w := parseBits bits
      if alikeAtTheGap hidden w then
        IO.println s!"  alike at the air gap: your {w.length}-pattern and the hidden one sound the same under every interview (the_audition_is_exact). the hidden one winds at {hidden.length}; the least alike pattern winds at its pages."
      else IO.println "  not alike: some word parts them. hear more, or make another."
      loop hidden fuel
  | ["fuel"] => IO.println s!"  fuel spent: {fuel}"; loop hidden fuel
  | ["quit"] => IO.println s!"the room is quiet. fuel spent: {fuel}"
  | _ => IO.println "  boxes | ask <box> <cells…> | widen <box> <cells…> | alike <a> <b> | hear 7 <k> | make 7 <t/f …> | fuel | quit"; loop hidden fuel

def main : IO Unit := do
  let book := words 4
  let seed ← match (← IO.getEnv "SEED") >>= String.toNat? with
    | some n => pure n
    | none => IO.rand 0 (book.length - 1)
  let hidden := (book[seed % book.length]?).getD [true]
  IO.println "the chinese room. six boxes behind an air gap, and a seventh grown from a seed no seat reads; you may only interview them. type `boxes`."
  loop hidden 0
