-------------------------- MODULE SingleLaneBridge --------------------------

\* A bridge over a river is only wide enough to permit a single lane of traffic.
\* Consequently, cars can only move concurrently if they are moving in the same 
\* direction. A safety violation occurs if two cars moving in different directions
\* enter the bridge at the same time.
\* To visualize the problem, refer to https://flylib.com/books/en/2.752.1.48/1/
   
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CarsRight, CarsLeft, Bridge, Positions

VARIABLES Location, WaitingBeforeBridge
vars ≜ ⟨Location, WaitingBeforeBridge⟩

StartPos ≜ CHOOSE min ∈ Positions : ∀ p ∈ Positions : min ≤ p
EndPos   ≜ CHOOSE max ∈ Positions : ∀ p ∈ Positions : max ≥ p

StartBridge ≜ CHOOSE min ∈ Bridge : ∀ e ∈ Bridge : min ≤ e
EndBridge   ≜ CHOOSE max ∈ Bridge : ∀ e ∈ Bridge : max ≥ e

ASSUME CarsRight ∩ CarsLeft = {}
ASSUME Cardinality(CarsRight ∪ CarsLeft ) ≠ 0
ASSUME StartPos < StartBridge ∧ EndPos > EndBridge ∧ Cardinality(Bridge) < Cardinality(Positions)


RECURSIVE SeqFromSet(_)
SeqFromSet(S) ≜ 
  IF S = {} THEN ⟨ ⟩ 
  ELSE LET x ≜ CHOOSE x ∈ S : TRUE
       IN  ⟨ x ⟩ ∘ SeqFromSet(S \ {x})

Cars ≜ CarsRight ∪ CarsLeft
CarsInBridge ≜ { c ∈ Cars : Location[c] ∈ Bridge }
CarsBeforeBridge ≜ { car ∈ CarsRight : EndPos - EndBridge = 1 } ∪ { car ∈ CarsLeft : StartBridge - StartPos = 1 }

RMove(pos) ≜ IF pos > StartPos THEN pos - 1 ELSE EndPos
LMove(pos) ≜ IF pos < EndPos THEN pos + 1 ELSE StartPos

NextLocation(car) ≜ IF car ∈ CarsRight THEN RMove(Location[car]) ELSE LMove(Location[car])

ChangeLocation(car) ≜
    ∧ IF ∨ car ∈ CarsRight ∧ NextLocation(car) = EndBridge + 1
         ∨ car ∈ CarsLeft ∧ NextLocation(car) = StartBridge - 1
        THEN WaitingBeforeBridge' = Append(WaitingBeforeBridge, car)
        ELSE UNCHANGED WaitingBeforeBridge
    ∧ Location' = [ Location EXCEPT ![car] = NextLocation(car) ]

HaveSameDirection(car) ≜
    ∨ car ∈ CarsRight ∧ ∀ c ∈ CarsInBridge : c ∈ CarsRight
    ∨ car ∈ CarsLeft ∧ ∀ c ∈ CarsInBridge : c ∈ CarsLeft

\* Actions
MoveOutsideBridge(car) ≜
    ∧ NextLocation(car) ∉ Bridge
    ∧ ChangeLocation(car)

MoveInsideBridge(car) ≜
    ∧ car ∈ CarsInBridge
    ∧ ∀ c ∈ Cars : Location[c] ≠ NextLocation(car)
    ∧ ChangeLocation(car)

EnterBridge ≜
    ∨  ∧ CarsInBridge = {}
       ∧ Len(WaitingBeforeBridge) ≠ 0
       ∧ Location' = [ Location EXCEPT ![Head(WaitingBeforeBridge)] = NextLocation(Head(WaitingBeforeBridge)) ]
       ∧ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)
    ∨  ∧ Len(WaitingBeforeBridge) ≠ 0
       ∧ Head(WaitingBeforeBridge) ∉ CarsInBridge
       ∧ HaveSameDirection(Head(WaitingBeforeBridge))
       ∧ ∀ c ∈ Cars : Location[c] ≠ NextLocation(Head(WaitingBeforeBridge))
       ∧ Location' = [ Location EXCEPT ![Head(WaitingBeforeBridge)] = NextLocation(Head(WaitingBeforeBridge)) ]
       ∧ WaitingBeforeBridge' = Tail(WaitingBeforeBridge)

Init ≜ 
    ∧ Location = [ c ∈ Cars ↦ IF c ∈ CarsRight THEN EndPos ELSE StartPos  ]
    ∧ WaitingBeforeBridge = SeqFromSet(CarsBeforeBridge)

Next ≜ ∃ car ∈ Cars : EnterBridge ∨ MoveOutsideBridge(car) ∨ MoveInsideBridge(car)

Fairness ≜
    ∧ ∀ car ∈ Cars : WF_vars(MoveOutsideBridge(car))
    ∧ ∀ car ∈ Cars : WF_vars(MoveInsideBridge(car))
    ∧ ∀ car ∈ Cars : WF_vars(EnterBridge)

Spec ≜ Init ∧ □[Next]_vars ∧ Fairness

Invariants ≜
    \* Two cars or more cannot be in the same location in the Bridge at the same time
    ∧ ∀ a,b ∈ Cars :
        ∧ Location[a] ∈ Bridge
        ∧ Location[a] = Location[b]
        ⇒ a = b
    \* The bridge capacity should be respected
    ∧ Cardinality(CarsInBridge) < Cardinality(Bridge) + 1
    \* Two cars of different directions can never be in the bridge
    ∧ ∀ ⟨r,l⟩ ∈ CarsRight × CarsLeft :
        ¬ (Location[r] ∈ Bridge ∧ Location[l] ∈ Bridge) 

TypeOK ≜
    ∧ Location ∈ [ Cars → Positions ]
    ∧ Len(WaitingBeforeBridge) ≤ Cardinality(Cars)

CarsInBridgeExitBridge ≜
    \* All cars eventually exit the Bridge 
    ∀ car ∈ Cars : Location[car] ∈ Bridge ↝ Location[car] ∉ Bridge

CarsEnterBridge ≜
    \* All cars eventually enter the bridge
    ∀ car ∈ Cars : Location[car] ∉ Bridge ↝ Location[car] ∈ Bridge

THEOREM Spec ⇒ □ Invariants

THEOREM Spec ⇒ □ TypeOK

THEOREM Spec ⇒ CarsInBridgeExitBridge
THEOREM Spec ⇒ CarsEnterBridge


=============================================================================
\* Modification History
\* Last modified Tue Oct 12 00:20:28 CEST 2021 by youne