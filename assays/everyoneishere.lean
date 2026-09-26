import Witness
open Room Face Witness
set_option autoImplicit false

-- EVERYONE IS HERE, as of the cut's landing (everyoneishere/docs/CUT.md, 2026-09-25), typed from that paper
-- alone and with no knowledge of its own history: not the product as it stands today, not the migration as a
-- diff. isaac, 19:07 and 19:21: "the entire EIH thing" as a foam pull request, "EIH without knowledge of its own
-- development history, the platonic ideal of EIH, maybe"; eih.lean, here.lean and everyone.feature ignored the
-- way the child-parent priming was. one type, one relation, one clock. a ROOM is the type: a wedding is a room,
-- a person is a room (their self-root), the side door is a room (the root); which of these a room is, is read,
-- not stored — a room with a Now is audible and is the thing paid for, a room without one is silent, connective
-- tissue. STANDING is the relation: a room stands at a table of another room — a vendor's self-root stands at
-- the wedding (the wedding reads a seat; the self-root reads a door), a wedding stands at the root (hosted), a
-- paid room stands at its payer's self-root. earshot is a table recognizing a seat back, and it is `hears`. the
-- COUNTER is the clock: every motion in a room takes a cell of that room's tape, the founding is #0 and is the
-- only word the room itself says, and no row in a room carries a stamp. in the treaty's terms: the house is a
-- face whose probes are (room, table) — the tables a room has, its tape, and its head — and whose answer at a
-- probe is that table's half: the store rows the table holds, each at its cell, and the standings read at it.
-- a standing's seat is the tables it hears in the room it stands at, with the room's tape and head always; a
-- silent room's seat is its doors, each a head and nothing else. the tape is the room's half of every motion —
-- who moved, at which table, what kind, at which cell — and a voice on it resolves only for a reader who hears
-- the table the standing is read at: a vendor resolves the couple's word at ✦ Couple as a voice and a table, a
-- guest reads that someone said a word there, a party's ✓ at ✦ Guests names itself to the couple and that party
-- alone. the sign of a ✓ (ack_pos · ack_neg) is the acks row's and never the tape's; `ready` reads an ack as
-- answered without it. a word, an ask, a ✓ or a store row takes a cell only while the room's air is on; a door
-- (stood, left, air) ticks in a silent room whatever the air. the crossing is not here: a room in this assay
-- has no history but its own tape.

namespace EveryoneIsHere.Treaty

-- a probe is (room, kind). the tape and the head are what every standing hears and what a door reads; the rest
-- are the tables, each the room's own; ✦ Guests is recognized party by party, so a party is its own probe.

def tapeK : Nat := 1

def headK : Nat := 2

def everyone : Nat := 3

def couple : Nat := 4

def vendors : Nat := 5

def now : Nat := 6

def seating : Nat := 7

def reach : Nat := 8

def guests : Nat := 9

def guestsOf (party : Nat) : Nat := 10 + party

def atADoor : Nat := 0

-- the kinds of a cell

def said : Nat := 1

def asked : Nat := 2

def ack : Nat := 3

def founded : Nat := 4

def stood : Nat := 5

def left : Nat := 6

def air : Nat := 7

-- the roles a standing can have; a room standing at a silent room has none

def asRoom : Nat := 0

def asCouple : Nat := 1

def asParty : Nat := 2

def asVendor : Nat := 3

def asPlanner : Nat := 4

def asGuest : Nat := 5

def asTeam : Nat := 6

structure Standing where
  id : Nat
  room : Nat
  atRoom : Nat
  tableKind : Nat
  role : Nat
  title : Nat

structure Cell where
  room : Nat
  n : Nat
  voice : Nat
  tableKind : Nat
  kind : Nat

structure Word where
  room : Nat
  cell : Nat
  voice : Nat
  tableKind : Nat
  body : Nat

structure Ask where
  room : Nat
  cell : Nat
  word : Nat
  voice : Nat
  ofWhom : Nat
  tableKind : Nat

structure Ack where
  room : Nat
  cell : Nat
  word : Nat
  voice : Nat
  pos : Bool
  tableKind : Nat

structure Now where
  room : Nat
  up : Bool
  payer : Nat

structure House where
  rooms : List (Nat × Nat)
  standings : List Standing
  hears : List (Nat × Nat × Nat)
  tape : List Cell
  words : List Word
  asks : List Ask
  acks : List Ack
  nows : List Now

def emptyHouse : House := ⟨[], [], [], [], [], [], [], []⟩

-- the tape, the count, the air

def tapeOf (h : House) (room : Nat) : List Cell := h.tape.filter (fun c => Nat.beq c.room room)

def countOf (h : House) (room : Nat) : Nat := (tapeOf h room).length

def nextCell (h : House) (room : Nat) : Nat := countOf h room

def nowOf (h : House) (room : Nat) : List Now := h.nows.filter (fun w => Nat.beq w.room room)

def audible (h : House) (room : Nat) : Bool := (nowOf h room).any (fun _ => true)

def airOn (h : House) (room : Nat) : Bool := (nowOf h room).any (fun w => w.up)

def payerOf (h : House) (room : Nat) : Nat :=
  match nowOf h room with
  | w :: _ => w.payer
  | [] => 0

def answered (h : House) (a : Ask) : Bool :=
  h.acks.any (fun k => Nat.beq k.room a.room && Nat.beq k.word a.word && Nat.beq k.voice a.ofWhom)

def openAsks (h : House) (room : Nat) : List Ask :=
  (h.asks.filter (fun a => Nat.beq a.room room)).filter (fun a => !(answered h a))

def readyAt (h : House) (room : Nat) : Bool := Nat.beq (openAsks h room).length 0

-- the face: what a probe answers. every row is tagged — 1 a cell of the tape, 2 the head, 3 a word, 4 an ask,
-- 5 a ✓ (its sign last), 6 the Now (ready, air, payer), 8 a standing read at this table.

def cellRows (h : House) (room : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (tapeOf h room).map (fun c => (1, c.n, c.voice, c.tableKind, c.kind))

def storeAt (h : House) (room k : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (h.words.filter (fun w => Nat.beq w.room room && Nat.beq w.tableKind k)).map (fun w => (3, w.cell, w.voice, w.tableKind, w.body))
  ++ (h.asks.filter (fun a => Nat.beq a.room room && Nat.beq a.tableKind k)).map (fun a => (4, a.cell, a.word, a.voice, a.ofWhom))
  ++ (h.acks.filter (fun a => Nat.beq a.room room && Nat.beq a.tableKind k)).map (fun a => (5, a.cell, a.word, a.voice, cond a.pos 1 0))
  ++ (h.standings.filter (fun s => Nat.beq s.atRoom room && Nat.beq s.tableKind k)).map (fun s => (8, s.id, s.room, s.role, s.title))

def nowRow (h : House) (room : Nat) : Nat × Nat × Nat × Nat × Nat :=
  (6, cond (readyAt h room) 1 0, cond (airOn h room) 1 0, payerOf h room, 0)

def heardAt (h : House) (p : Nat × Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  cond (Nat.beq p.2 tapeK) (cellRows h p.1)
    (cond (Nat.beq p.2 headK) [(2, countOf h p.1 - 1, 0, 0, 0)]
      (cond (Nat.beq p.2 now) (nowRow h p.1 :: storeAt h p.1 now)
        (storeAt h p.1 p.2)))

def roomFace : Face := ⟨House, Nat × Nat, List (Nat × Nat × Nat × Nat × Nat), heardAt⟩

instance : BEq roomFace.Ans := inferInstanceAs (BEq (List (Nat × Nat × Nat × Nat × Nat)))

-- the head and `ready` are readings at one probe each: the head at the door, ready at ✦ Now

def headRead : List (Nat × Nat × Nat × Nat × Nat) → Nat
  | [] => 0
  | t :: _ => t.2.1

def headOf (h : House) (room : Nat) : Nat := headRead (heardAt h (room, headK))

def readyRead : List (Nat × Nat × Nat × Nat × Nat) → Bool
  | [] => false
  | t :: _ => Nat.beq t.2.1 1

def ready (h : House) (room : Nat) : Bool := readyRead (heardAt h (room, now))

-- seats: a standing hears the tables `hears` gives it in the room it stands at, and the room's tape and head;
-- ✦ Guests opens into one probe per party. a silent room's seat is its doors — the rooms it stands at and the
-- rooms standing at it — each read at its head alone; a room with a Now has no doors.

def standingOf (h : House) (sid : Nat) : List Standing := h.standings.filter (fun s => Nat.beq s.id sid)

def partiesOf (h : House) (room : Nat) : List Nat :=
  (h.standings.filter (fun s => Nat.beq s.atRoom room && Nat.beq s.role asGuest)).map (·.tableKind)

def probesOf (h : House) (room k : Nat) : List (Nat × Nat) :=
  cond (Nat.beq k guests) ((partiesOf h room).map (fun p => (room, p))) [(room, k)]

def seatOf (h : House) (sid : Nat) : List (Nat × Nat) :=
  match standingOf h sid with
  | s :: _ =>
      joinMap (fun t => probesOf h s.atRoom t.2.1) (h.hears.filter (fun t => Nat.beq t.1 s.atRoom && Nat.beq t.2.2 sid))
        ++ [(s.atRoom, tapeK), (s.atRoom, headK)]
  | [] => []

def doorsOf (h : House) (room : Nat) : List Nat :=
  cond (audible h room) []
    ((h.standings.filter (fun s => Nat.beq s.room room)).map (·.atRoom)
      ++ (h.standings.filter (fun s => Nat.beq s.atRoom room)).map (·.room))

def homeSeat (h : House) (room : Nat) : List (Nat × Nat) := (doorsOf h room).map (fun d => (d, headK))

def pbeq (a b : Nat × Nat) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2

-- what a seat reads: its words, its ✓s with their signs, and the tape with each voice resolved against the
-- standings its tables gave it — a voice it cannot resolve reads as 0, someone.

def cellsOfWords (a : List (Nat × Nat × Nat × Nat × Nat)) : List Nat :=
  (a.filter (fun t => Nat.beq t.1 3)).map (fun t => t.2.1)

def inbox (h : House) (sid : Nat) : List Nat := joinMap cellsOfWords (reads roomFace (seatOf h sid) h)

def sees (h : House) (sid cell : Nat) : Bool := enrolled Nat.beq (inbox h sid) cell

def acksRead (h : House) (s : List (Nat × Nat)) : List (Nat × Bool) :=
  joinMap (fun a => (a.filter (fun t => Nat.beq t.1 5)).map (fun t => (t.2.1, Nat.beq t.2.2.2.2 1))) (reads roomFace s h)

def namesOf (rd : List (List (Nat × Nat × Nat × Nat × Nat))) : List Nat :=
  joinMap (fun a => (a.filter (fun t => Nat.beq t.1 8)).map (fun t => t.2.1)) rd

def tapeRowsOf (rd : List (List (Nat × Nat × Nat × Nat × Nat))) : List (Nat × Nat × Nat × Nat × Nat) :=
  joinMap (fun a => a.filter (fun t => Nat.beq t.1 1)) rd

def voicesRead (rd : List (List (Nat × Nat × Nat × Nat × Nat))) : List (Nat × Nat × Nat × Nat) :=
  (tapeRowsOf rd).map (fun t => (t.2.1, cond (enrolled Nat.beq (namesOf rd) t.2.2.1) t.2.2.1 0, t.2.2.2.1, t.2.2.2.2))

def voices (h : House) (s : List (Nat × Nat)) : List (Nat × Nat × Nat × Nat) := voicesRead (reads roomFace s h)

def voiceAt (h : House) (s : List (Nat × Nat)) (n : Nat) : Nat :=
  match (voices h s).filter (fun t => Nat.beq t.1 n) with
  | t :: _ => t.2.1
  | [] => 0

def cellAt (h : House) (room n : Nat) : Nat × Nat × Nat × Nat :=
  match (tapeOf h room).filter (fun c => Nat.beq c.n n) with
  | c :: _ => (c.n, c.voice, c.tableKind, c.kind)
  | [] => (0, 0, 0, 0)

def handleOf (h : House) (room : Nat) : Nat :=
  match h.rooms.filter (fun r => Nat.beq r.1 room) with
  | r :: _ => r.2
  | [] => 0

def roomBy (h : House) (handle : Nat) : Nat :=
  match h.rooms.filter (fun r => Nat.beq r.2 handle) with
  | r :: _ => r.1
  | [] => 0

def cellBy (h : House) (handle n : Nat) : Nat × Nat × Nat × Nat := cellAt h (roomBy h handle) n

def distinct : List Nat → Bool
  | [] => true
  | x :: r => !(enrolled Nat.beq r x) && distinct r

-- the motions. every one is a cell taken by the trigger, never by the mover; a word, an ask, a ✓ and a store
-- row need air; a door ticks in a silent room, and a room with a Now has no door side.

def tick (h : House) (room voice tableKind kind : Nat) : House :=
  { h with tape := h.tape ++ [⟨room, nextCell h room, voice, tableKind, kind⟩] }

def coarse (k : Nat) : Nat := cond (Nat.ble 10 k) guests k

def known (h : House) (room : Nat) : Bool := h.rooms.any (fun r => Nat.beq r.1 room)

def foundAt (h : House) (room handle : Nat) : House :=
  cond (known h room) h (tick { h with rooms := h.rooms ++ [(room, handle)] } room 0 atADoor founded)

def hearConcerns : Nat → List Nat
  | 1 => [everyone, couple, now, seating, reach, guests]
  | 2 => [everyone, now, seating]
  | 3 => [everyone, vendors, now]
  | 4 => [everyone, vendors, now, seating, reach, guests]
  | 5 => [now]
  | 6 => [everyone, now, seating]
  | _ => []

def seatSide (h : House) (s : Standing) (kind : Nat) : House := tick h s.atRoom s.id (coarse s.tableKind) kind

def doorSide (h : House) (s : Standing) (kind : Nat) : House :=
  cond (audible h s.room) h (tick h s.room s.id atADoor kind)

def standAt (h : House) (s : Standing) (extra : List Nat) : House :=
  doorSide
    (seatSide { h with standings := h.standings ++ [s],
                       hears := h.hears ++ (hearConcerns s.role ++ extra).map (fun k => (s.atRoom, k, s.id)) } s stood)
    s stood

def leaveAt (h : House) (sid : Nat) : House :=
  match standingOf h sid with
  | s :: _ =>
      doorSide
        (seatSide { h with standings := h.standings.filter (fun t => !(Nat.beq t.id sid)),
                           hears := h.hears.filter (fun t => !(Nat.beq t.2.2 sid)) } s left)
        s left
  | [] => h

def setNow (h : House) (room : Nat) (up : Bool) (payer : Nat) : House :=
  { h with nows := h.nows.filter (fun w => !(Nat.beq w.room room)) ++ [⟨room, up, payer⟩] }

def airAt (h : House) (room : Nat) (up : Bool) (payer : Nat) : House :=
  cond (audible h payer)
    (tick (setNow h room up payer) room 0 now air)
    (tick (tick (setNow h room up payer) room 0 now air) payer 0 atADoor air)

def landWord (h : House) (room voice k body : Nat) : House :=
  tick { h with words := h.words ++ [⟨room, nextCell h room, voice, k, body⟩] } room voice (coarse k) said

def sayAt (h : House) (room voice k body : Nat) : House := cond (airOn h room) (landWord h room voice k body) h

def tableOfWord (h : House) (room cell : Nat) : Nat :=
  match h.words.filter (fun w => Nat.beq w.room room && Nat.beq w.cell cell) with
  | w :: _ => w.tableKind
  | [] => 0

def landAsk (h : House) (room word voice ofWhom : Nat) : House :=
  tick { h with asks := h.asks ++ [⟨room, nextCell h room, word, voice, ofWhom, tableOfWord h room word⟩] }
    room voice (coarse (tableOfWord h room word)) asked

def askAt (h : House) (room word voice ofWhom : Nat) : House := cond (airOn h room) (landAsk h room word voice ofWhom) h

def landAck (h : House) (room word voice : Nat) (pos : Bool) : House :=
  tick { h with acks := h.acks ++ [⟨room, nextCell h room, word, voice, pos, tableOfWord h room word⟩] }
    room voice (coarse (tableOfWord h room word)) ack

def ackAt (h : House) (room word voice : Nat) (pos : Bool) : House := cond (airOn h room) (landAck h room word voice pos) h

inductive Act where
  | found (room handle : Nat)
  | stand (s : Standing) (extra : List Nat)
  | leave (sid : Nat)
  | air (room : Nat) (up : Bool) (payer : Nat)
  | say (room voice tableKind body : Nat)
  | ask (room word voice ofWhom : Nat)
  | ack (room word voice : Nat) (pos : Bool)

def act (h : House) : Act → House
  | .found room handle => foundAt h room handle
  | .stand s extra => standAt h s extra
  | .leave sid => leaveAt h sid
  | .air room up payer => airAt h room up payer
  | .say room voice k body => sayAt h room voice k body
  | .ask room word voice ofWhom => askAt h room word voice ofWhom
  | .ack room word voice pos => ackAt h room word voice pos

def houseMachine : Machine Act House := ⟨House, emptyHouse, act, fun h => h⟩

def house (w : List Act) : House := park houseMachine emptyHouse w

-- the cast: the demo's people, each a silent room of their own; the root; one wedding, founded by maya, aired
-- for a Now she pays for, hosted at the root. the standings: the couple, a planner, three vendors (a venue
-- hears ✦ Seating, the one wall a vendor kind bore), one of the party helping with the day (everyone, now and
-- seating, never ✦ Couple: the app's narrowing, a wall at last), and a guest — a seat the way a vendor is.

def root : Nat := 0

def maya : Nat := 1

def james : Nat := 2

def ava : Nat := 3

def sofia : Nat := 4

def jordan : Nat := 5

def dana : Nat := 6

def linda : Nat := 7

def rose : Nat := 8

def wedding : Nat := 20

def mayaAt : Standing := ⟨31, maya, wedding, everyone, asCouple, 1⟩

def jamesAt : Standing := ⟨32, james, wedding, everyone, asCouple, 1⟩

def avaAt : Standing := ⟨33, ava, wedding, everyone, asPlanner, 2⟩

def sofiaAt : Standing := ⟨34, sofia, wedding, everyone, asVendor, 3⟩

def jordanAt : Standing := ⟨35, jordan, wedding, everyone, asVendor, 4⟩

def danaAt : Standing := ⟨36, dana, wedding, everyone, asVendor, 5⟩

def lindaAt : Standing := ⟨37, linda, wedding, everyone, asParty, 6⟩

def roseAt : Standing := ⟨38, rose, wedding, guestsOf 1, asGuest, 0⟩

def weddingHosted : Standing := ⟨21, wedding, root, atADoor, asRoom, 0⟩

def weddingPaid : Standing := ⟨22, wedding, maya, atADoor, asRoom, 0⟩

def opening : List Act :=
  [.found root 100, .found maya 101, .found james 102, .found ava 103, .found sofia 104, .found jordan 105,
   .found dana 106, .found linda 107, .found rose 108, .found wedding 120,
   .stand mayaAt [], .air wedding true maya, .stand weddingPaid [], .stand weddingHosted [],
   .stand jamesAt [], .stand avaAt [], .stand sofiaAt [], .stand jordanAt [], .stand danaAt [seating],
   .stand lindaAt [], .stand roseAt [guestsOf 1]]

-- the wedding's tape after the opening: #0 founded, #1 maya stood, #2 air, #3–#8 the others stood, #9 rose stood
-- at ✦ Guests. then the words, #10 on: the couple's own word (#10), the caterer at ✦ Vendors (#11), a word at
-- ✦ Everyone with three asks on it (#12–#15) and two ✓s (#16, #17), the invitation to rose's party with its ask
-- (#18, #19), the venue's chart move (#20), the planner's itinerary row (#21) and her ★ on it (#22).

def script (ours : Nat) : List Act :=
  opening ++
  [.say wedding 31 couple ours,
   .say wedding 34 vendors 101,
   .say wedding 31 everyone 102,
   .ask wedding 12 31 34, .ask wedding 12 31 35, .ask wedding 12 31 36,
   .ack wedding 12 34 true, .ack wedding 12 35 true,
   .say wedding 31 (guestsOf 1) 108,
   .ask wedding 18 31 38,
   .say wedding 36 seating 107,
   .say wedding 33 now 1630,
   .ask wedding 21 33 33]

def demo : House := house (script 111)

def demo' : House := house (script 999)

def demoStar : House := park houseMachine demo [.ack wedding 12 36 true, .ack wedding 18 38 true]

def demoAcked : House := park houseMachine demoStar [.ack wedding 21 33 true]

def demoNo : House := park houseMachine demo [.ack wedding 12 36 true, .ack wedding 18 38 false, .ack wedding 21 33 true]

def demoOut : House := park houseMachine demo [.air wedding false maya]

def demoLeft : House := leaveAt demoOut 34

def demoSaid : House := sayAt demo wedding 31 couple 7

def people : List Nat := [31, 32, 33, 34, 35, 36, 37]

def others : List Nat := [33, 34, 35, 36, 37, 38]

def humanSeats (h : House) : List (List (Nat × Nat)) := people.map (seatOf h)

def otherSeats (h : House) : List (List (Nat × Nat)) := others.map (seatOf h)

-- the clock: order is n, #0 is the founding and the room's only word, a number once written never moves
#guard (cellRows demo wedding).map (·.2.1) == List.range 23
#guard headOf demo wedding == 22
#guard headOf demo maya == 3
#guard headOf demo root == 1
#guard cellAt demo wedding 0 == (0, 0, atADoor, founded)
#guard cellAt demo wedding 1 == (1, 31, everyone, stood)
#guard cellAt demo wedding 2 == (2, 0, now, air)
#guard cellAt demo wedding 9 == (9, 38, guests, stood)
#guard cellAt demo wedding 10 == (10, 31, couple, said)
#guard cellAt demo wedding 22 == (22, 33, now, asked)
#guard (tapeOf demo wedding).all (fun c => !(Nat.beq c.voice 0) || Nat.beq c.kind founded || Nat.beq c.kind air)
#guard headOf demoSaid wedding == 23
#guard (cellRows demoSaid wedding).take 23 == cellRows demo wedding

-- a silent room's tape ticks for its doors and nothing else: founded, stood at a wedding, air for a Now it pays for
#guard cellAt demo maya 0 == (0, 0, atADoor, founded)
#guard cellAt demo maya 1 == (1, 31, atADoor, stood)
#guard cellAt demo maya 2 == (2, 0, atADoor, air)
#guard cellAt demo maya 3 == (3, 22, atADoor, stood)
#guard cellAt demo root 1 == (1, 21, atADoor, stood)
#guard cellAt demo sofia 1 == (1, 34, atADoor, stood)
#guard cellAt demo wedding 5 == (5, 34, everyone, stood)
#guard airOn demo maya == false
#guard audible demo maya == false
#guard headOf (sayAt demo maya 31 everyone 5) maya == 3

-- handles: one namespace, and handle#n names a cell from anywhere
#guard distinct (demo.rooms.map (·.2))
#guard handleOf demo wedding == 120
#guard roomBy demo 120 == wedding
#guard cellBy demo 120 10 == cellAt demo wedding 10

-- air: a word, an ask, a ✓ need it; a door ticks without it; a room whose air is out hosts no doors
#guard airOn demo wedding
#guard airOn demoOut wedding == false
#guard audible demoOut wedding
#guard headOf demoOut wedding == 23
#guard cellAt demoOut wedding 23 == (23, 0, now, air)
#guard cellAt demoOut maya 4 == (4, 0, atADoor, air)
#guard headOf (sayAt demoOut wedding 31 everyone 5) wedding == 23
#guard headOf (askAt demoOut wedding 12 31 37) wedding == 23
#guard headOf (ackAt demoOut wedding 12 36 true) wedding == 23
#guard headOf demoLeft wedding == 24
#guard cellAt demoLeft wedding 24 == (24, 34, everyone, left)
#guard cellAt demoLeft sofia 2 == (2, 34, atADoor, left)
#guard inbox demoLeft 31 == inbox demoOut 31
#guard homeSeat demoOut wedding == []
#guard homeSeat demoOut sofia == [(wedding, headK)]

-- a host's tape never ticks for a hosted room's motion; a door reads the head and nothing else
#guard cellRows demoSaid root == cellRows demo root
#guard cellRows demoSaid maya == cellRows demo maya
#guard homeSeat demo wedding == []
#guard homeSeat demo root == [(wedding, headK)]
#guard homeSeat demo sofia == [(wedding, headK)]
#guard homeSeat demo maya == [(wedding, headK), (wedding, headK)]
#guard reads roomFace (homeSeat demo sofia) demo == [[(2, 22, 0, 0, 0)]]
#guard reads roomFace (homeSeat demo sofia) demoSaid == [[(2, 23, 0, 0, 0)]]
#guard reads roomFace (homeSeat demo sofia) demo == reads roomFace (homeSeat demo sofia) demo'

-- earshot: who hears what
#guard (seatOf demo 38).length == 4
#guard seatOf demo 38 == [(wedding, now), (wedding, guestsOf 1), (wedding, tapeK), (wedding, headK)]
#guard enrolled pbeq (seatOf demo 31) (wedding, guestsOf 1)
#guard enrolled pbeq (seatOf demo 33) (wedding, guestsOf 1)
#guard enrolled pbeq (seatOf demo 34) (wedding, guestsOf 1) == false
#guard enrolled pbeq (seatOf demo 36) (wedding, seating)
#guard enrolled pbeq (seatOf demo 34) (wedding, seating) == false
#guard enrolled pbeq (seatOf demo 37) (wedding, couple) == false
#guard enrolled pbeq (seatOf demo 37) (wedding, guestsOf 1) == false
#guard enrolled pbeq (earshot roomFace (otherSeats demo)) (wedding, couple) == false
#guard enrolled pbeq (earshot roomFace [seatOf demo 31, seatOf demo 32]) (wedding, couple)
#guard enrolled pbeq (earshot roomFace (humanSeats demo)) (wedding, guestsOf 1)
#guard enrolled pbeq (earshot roomFace ([34, 35, 36, 37].map (seatOf demo))) (wedding, guestsOf 1) == false

-- the words: seen where the table is heard
#guard sees demo 31 10
#guard sees demo 32 10
#guard sees demo 33 10 == false
#guard sees demo 34 10 == false
#guard sees demo 37 10 == false
#guard sees demo 38 10 == false
#guard sees demo 34 11
#guard sees demo 31 11 == false
#guard sees demo 37 12
#guard sees demo 38 12 == false
#guard sees demo 38 18
#guard sees demo 33 18
#guard sees demo 31 18
#guard sees demo 34 18 == false
#guard sees demo 37 18 == false
#guard sees demo 36 20
#guard sees demo 37 20
#guard sees demo 34 20 == false
#guard sees demo 38 21
#guard sees demo 34 21
#guard inbox demo 34 == [12, 11, 21]
#guard inbox demo 38 == [21, 18]

-- the grain: the tape is read whole by every standing, and a voice resolves only where its table is heard
#guard (voices demo (seatOf demo 38)).length == 23
#guard voiceAt demo (seatOf demo 34) 10 == 31
#guard voiceAt demo (seatOf demo 37) 10 == 31
#guard voiceAt demo (seatOf demo 38) 10 == 0
#guard voiceAt demo (seatOf demo 31) 9 == 38
#guard voiceAt demo (seatOf demo 33) 9 == 38
#guard voiceAt demo (seatOf demo 38) 9 == 38
#guard voiceAt demo (seatOf demo 34) 9 == 0
#guard voiceAt demo (seatOf demo 38) 0 == 0
#guard voices demo (seatOf demo 38) == voices demo' (seatOf demo' 38)
#guard voices demo (seatOf demo 34) == voices demo' (seatOf demo' 34)

-- the ✓: a sign on the row, none on the tape; ready reads an ack as answered without it; a ★ is one cell and
-- keeps everyone waiting; letting go is one's own ✓
#guard (openAsks demo wedding).map (·.cell) == [15, 19, 22]
#guard ready demo wedding == false
#guard ready demoStar wedding == false
#guard (openAsks demoStar wedding).map (·.cell) == [22]
#guard ready demoAcked wedding
#guard ready demoNo wedding
#guard cellAt demoAcked wedding 24 == (24, 38, guests, ack)
#guard cellAt demoAcked wedding 25 == (25, 33, now, ack)
#guard cellRows demoAcked wedding == cellRows demoNo wedding
#guard acksRead demoAcked (seatOf demoAcked 31) == [(16, true), (17, true), (23, true), (25, true), (24, true)]
#guard acksRead demoNo (seatOf demoNo 31) == [(16, true), (17, true), (23, true), (25, true), (24, false)]
#guard acksRead demoNo (seatOf demoNo 38) == [(25, true), (24, false)]
#guard acksRead demoNo (seatOf demoNo 34) == [(16, true), (17, true), (23, true), (25, true)]
#guard acksRead demoNo (seatOf demoNo 34) == acksRead demoAcked (seatOf demoAcked 34)
#guard voiceAt demoAcked (seatOf demoAcked 31) 24 == 38
#guard voiceAt demoAcked (seatOf demoAcked 33) 24 == 38
#guard voiceAt demoAcked (seatOf demoAcked 38) 24 == 38
#guard voiceAt demoAcked (seatOf demoAcked 34) 24 == 0
#guard voiceAt demoAcked (seatOf demoAcked 37) 24 == 0

-- witness: two houses that differ only in the couple's word read the same at every seat off ✦ Couple
#guard seatOf demo 37 == seatOf demo' 37
#guard reads roomFace (seatOf demo 37) demo == reads roomFace (seatOf demo 37) demo'
#guard reads roomFace (seatOf demo 34) demo == reads roomFace (seatOf demo 34) demo'
#guard reads roomFace (seatOf demo 38) demo == reads roomFace (seatOf demo 38) demo'
#guard reads roomFace (seatOf demo 33) demo == reads roomFace (seatOf demo 33) demo'
#guard (reads roomFace (seatOf demo 31) demo == reads roomFace (seatOf demo 31) demo') == false
#guard (reads roomFace (seatOf demo 32) demo == reads roomFace (seatOf demo 32) demo') == false

-- the walls

theorem a_word_needs_air (h : House) (room voice k body : Nat) (ha : airOn h room = false) :
    sayAt h room voice k body = h := by
  show cond (airOn h room) (landWord h room voice k body) h = h
  rw [ha]
  rfl

theorem an_ask_needs_air (h : House) (room word voice ofWhom : Nat) (ha : airOn h room = false) :
    askAt h room word voice ofWhom = h := by
  show cond (airOn h room) (landAsk h room word voice ofWhom) h = h
  rw [ha]
  rfl

theorem a_check_needs_air (h : House) (room word voice : Nat) (pos : Bool) (ha : airOn h room = false) :
    ackAt h room word voice pos = h := by
  show cond (airOn h room) (landAck h room word voice pos) h = h
  rw [ha]
  rfl

theorem the_couples_table_is_a_wall_at_every_other_seat (h h' : House) (hd : differOnly roomFace h h' (wedding, couple))
    (s : List (Nat × Nat)) (hs : ¬ hears roomFace s (wedding, couple)) : reads roomFace s h = reads roomFace s h' := sorry

theorem the_room_reads_the_same_whatever_the_couple_say (h h' : House) (hd : differOnly roomFace h h' (wedding, couple))
    (seats : List (List (Nat × Nat))) (hs : ∀ s, s ∈ seats → ¬ hears roomFace s (wedding, couple)) :
    witnessed roomFace seats h h' := sorry

theorem a_partys_rows_are_a_wall_off_the_party (h h' : House) (hd : differOnly roomFace h h' (wedding, guestsOf 1))
    (s : List (Nat × Nat)) (hs : ¬ hears roomFace s (wedding, guestsOf 1)) : reads roomFace s h = reads roomFace s h' := sorry

theorem a_door_reads_the_head_alone (h h' : House) (k : Nat) (hd : differOnly roomFace h h' (wedding, k))
    (hs : ¬ hears roomFace (homeSeat h sofia) (wedding, k)) :
    reads roomFace (homeSeat h sofia) h = reads roomFace (homeSeat h sofia) h' := sorry

theorem the_couples_seat_parts_them (h h' : House) (hp : roomFace.obs h (wedding, couple) ≠ roomFace.obs h' (wedding, couple))
    (hs : hears roomFace (seatOf h 31) (wedding, couple)) :
    reads roomFace (seatOf h 31) h ≠ reads roomFace (seatOf h 31) h' := sorry

theorem the_head_is_a_reading (n : Nat) : Derived roomFace (fun h => headOf h wedding = n) :=
  a_role_read_at_a_probe_is_derived roomFace (wedding, headK) (fun a => headRead a = n)

theorem ready_is_a_reading (b : Bool) : Derived roomFace (fun h => ready h wedding = b) :=
  a_role_read_at_a_probe_is_derived roomFace (wedding, now) (fun a => readyRead a = b)

theorem the_voices_are_a_reading (s : List (Nat × Nat)) (v : List (Nat × Nat × Nat × Nat)) :
    Derived roomFace (fun h => voices h s = v) := sorry

theorem the_sign_is_off_the_tape (h : House) (word voice : Nat) (p q : Bool) :
    cellRows (ackAt h wedding word voice p) wedding = cellRows (ackAt h wedding word voice q) wedding := by
  unfold ackAt
  cases airOn h wedding <;> rfl

theorem the_filter_crosses_the_append {A : Type} (q : A → Bool) :
    ∀ l m : List A, (l ++ m).filter q = l.filter q ++ m.filter q
  | [], _ => rfl
  | a :: l, m => by
      cases hq : q a with
      | true =>
          rw [List.cons_append, List.filter_cons_of_pos hq, List.filter_cons_of_pos hq]
          exact congrArg (List.cons a) (the_filter_crosses_the_append q l m)
      | false =>
          rw [List.cons_append, List.filter_cons_of_neg (ne_true_of_eq_false hq),
              List.filter_cons_of_neg (ne_true_of_eq_false hq)]
          exact the_filter_crosses_the_append q l m

theorem the_room_is_the_widest_seat (s : List (Nat × Nat)) (h h' : House) (hr : reads roomFace s h ≠ reads roomFace s h') :
    ¬ alike roomFace h h' := sorry

theorem two_houses_part_only_at_a_probe (h h' : House) :
    alike roomFace h h' ↔ ∀ q, sound roomFace h q = sound roomFace h' q :=
  ⟨fun ha q => no_interview_parts_the_alike roomFace ha q, fun hq => the_sounding_reads_the_alike roomFace hq⟩

theorem a_hosts_tape_never_ticks_for_a_hosted_word (h : House) (voice k body : Nat) :
    cellRows (sayAt h wedding voice k body) root = cellRows h root := by
  unfold sayAt
  cases airOn h wedding
  · rfl
  · show ((h.tape ++ [(⟨wedding, nextCell h wedding, voice, coarse k, said⟩ : Cell)]).filter (fun c : Cell => Nat.beq c.room root)).map
        (fun c : Cell => (1, c.n, c.voice, c.tableKind, c.kind)) = cellRows h root
    rw [the_filter_crosses_the_append, List.filter_cons_of_neg (by show ¬ Nat.beq wedding root = true; decide),
        List.filter_nil, the_append_rests]
    rfl

theorem a_tick_keeps_every_cell (h : House) (room voice k kind r : Nat) (t : Nat × Nat × Nat × Nat × Nat)
    (ht : t ∈ cellRows h r) : t ∈ cellRows (tick h room voice k kind) r := by
  show t ∈ ((h.tape ++ [(⟨room, nextCell h room, voice, k, kind⟩ : Cell)]).filter (fun c : Cell => Nat.beq c.room r)).map
      (fun c : Cell => (1, c.n, c.voice, c.tableKind, c.kind))
  rw [the_filter_crosses_the_append, map_crosses_append]
  exact mem_append_left _ ht

end EveryoneIsHere.Treaty
