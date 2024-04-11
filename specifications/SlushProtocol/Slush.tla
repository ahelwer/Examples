----------------------------- MODULE Slush ---------------------------------
(**************************************************************************)
(* A specification of the Slush protocol, a very simple probabilistic     *)
(* consensus algorithm in the Avalanche family. Given that TLA⁺ has no    *) 
(* probabilistic modeling capabilities this spec is of limited utility,   *)
(* beyond serving as executable pseudocode. For example, we would want to *)
(* ask questions like "what is the maximum probability of not converging  *)
(* with N iterations, K sample size, and T flip threshold" but we cannot. *)
(* These questions can be answered in probabilistic modeling languages    *)
(* like PRISM, but it is difficult to get PRISM working on this problem.  *)
(* See https://github.com/ahelwer/avalanche-analysis/                     *)
(**************************************************************************)

EXTENDS
  Naturals,
  FiniteSets,
  Sequences

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold

ASSUME
  ∧ Cardinality(Node) = Cardinality(SlushLoopProcess)
  ∧ Cardinality(Node) = Cardinality(SlushQueryProcess)
  ∧ SlushIterationCount ∈ ℕ
  ∧ SampleSetSize ∈ ℕ
  ∧ PickFlipThreshold ∈ ℕ

ASSUME HostMappingType ≜
  ∧ Cardinality(Node) = Cardinality(HostMapping)
  ∧ ∀ mapping ∈ HostMapping :
    ∧ Cardinality(mapping) = 3
    ∧ ∃ e ∈ mapping : e ∈ Node
    ∧ ∃ e ∈ mapping : e ∈ SlushLoopProcess
    ∧ ∃ e ∈ mapping : e ∈ SlushQueryProcess

HostOf[pid ∈ SlushLoopProcess ∪ SlushQueryProcess] ≜
  CHOOSE n ∈ Node :
    ∧ ∃ mapping ∈ HostMapping :
      ∧ n ∈ mapping
      ∧ pid ∈ mapping

----------------------------------------------------------------------------

(*--algorithm Slush
variables
    pick = [node ∈ Node ↦ NoColor];
    
    message = {};

define
  Red ≜ "Red"

  Blue ≜ "Blue"

  Color ≜ {Red, Blue}

  NoColor ≜ CHOOSE c : c ∉ Color

  QueryMessageType ≜ "QueryMessageType"

  QueryReplyMessageType ≜ "QueryReplyMessageType"

  TerminationMessageType ≜ "TerminationMessageType"

  QueryMessage ≜ [
    type  : {QueryMessageType},
    src   : SlushLoopProcess,
    dst   : SlushQueryProcess,
    color : Color
  ]

  QueryReplyMessage ≜ [
    type  : {QueryReplyMessageType},
    src   : SlushQueryProcess,
    dst   : SlushLoopProcess,
    color : Color
  ]

  TerminationMessage ≜ [
    type  : {TerminationMessageType},
    pid   : SlushLoopProcess
  ]

  Message ≜
    QueryMessage
    ∪ QueryReplyMessage
    ∪ TerminationMessage

  NoMessage ≜ CHOOSE m : m ∉ Message

  TypeInvariant ≜
    ∧ pick ∈ [Node → Color ∪ {NoColor}]
    ∧ message ⊆ Message    

  PendingQueryMessage(pid) ≜ {
    m ∈ message :
      ∧ m.type = QueryMessageType 
      ∧ m.dst = pid
  }

  PendingQueryReplyMessage(pid) ≜ {
    m ∈ message :
      ∧ m.type = QueryReplyMessageType 
      ∧ m.dst = pid
  }

  Terminate ≜
    message = TerminationMessage

  Pick(pid) ≜ pick[HostOf[pid]]

end define

process SlushQuery ∈ SlushQueryProcess
begin
  QueryReplyLoop: while ¬Terminate do

    WaitForQueryMessageOrTermination:
      await PendingQueryMessage(self) ≠ {} ∨ Terminate;
      if Terminate then
        goto QueryReplyLoop;
      end if;

    RespondToQueryMessage:
      with msg ∈ PendingQueryMessage(self), color = IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) do
        pick[HostOf[self]] ≔ color;
        message ≔ (message \ {msg}) ∪
          {[type  ↦ QueryReplyMessageType,
          src     ↦ self,
          dst     ↦ msg.src,
          color   ↦ color]};
      end with;

  end while;
  
end process;

process SlushLoop ∈ SlushLoopProcess
variables
  sampleSet = {},
  loopVariant = 0
begin
  RequireColorAssignment: 
    await Pick(self) ≠ NoColor;

  ExecuteSlushLoop: while loopVariant < SlushIterationCount do

    QuerySampleSet:
      with
        possibleSampleSet ∈ 
          LET
            otherNodes ≜ Node \ {HostOf[self]}
            otherQueryProcesses ≜ {pid ∈ SlushQueryProcess : HostOf[pid] ∈ otherNodes}
          IN {pidSet ∈ SUBSET otherQueryProcesses : Cardinality(pidSet) = SampleSetSize}
      do
        sampleSet ≔ possibleSampleSet;
        message ≔ message ∪
          {[type  ↦ QueryMessageType,
          src     ↦ self,
          dst     ↦ pid,
          color   ↦ Pick(self)] :
            pid ∈ sampleSet};
      end with;

    TallyQueryReplies:
      await
        ∧ ∀ pid ∈ sampleSet :
          ∧ ∃ msg ∈ PendingQueryReplyMessage(self) :
            ∧ msg.src = pid;
      with
        redTally = Cardinality(
          {msg ∈ PendingQueryReplyMessage(self) :
            ∧ msg.src ∈ sampleSet
            ∧ msg.color = Red}),
        blueTally = Cardinality(
          {msg ∈ PendingQueryReplyMessage(self) :
            ∧ msg.src ∈ sampleSet
            ∧ msg.color = Blue})
      do
        if redTally ≥ PickFlipThreshold then
          pick[HostOf[self]] ≔ Red;
        elsif blueTally ≥ PickFlipThreshold then
          pick[HostOf[self]] ≔ Blue;
        end if;
      end with;
      message ≔ message \
        {msg ∈ message :
          ∧ msg.type = QueryReplyMessageType
          ∧ msg.src ∈ sampleSet
          ∧ msg.dst = self};
      sampleSet ≔ {};
      loopVariant ≔ loopVariant + 1;

  end while;

  SlushLoopTermination: message ≔ message ∪ {[
    type ↦ TerminationMessageType, pid ↦ self
  ]}

end process;

process ClientRequest = "ClientRequest"
begin
  ClientRequestLoop: while ∃ n ∈ Node : pick[n] = NoColor do
    AssignColorToNode:
      with node ∈ Node, color ∈ Color do
        if pick[node] = NoColor then
          pick[node] ≔ color;
        end if;
      end with;
  end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES pick, message, pc

(* define statement *)
Red ≜ "Red"

Blue ≜ "Blue"

Color ≜ {Red, Blue}

NoColor ≜ CHOOSE c : c ∉ Color

QueryMessageType ≜ "QueryMessageType"

QueryReplyMessageType ≜ "QueryReplyMessageType"

TerminationMessageType ≜ "TerminationMessageType"

QueryMessage ≜ [
  type  : {QueryMessageType},
  src   : SlushLoopProcess,
  dst   : SlushQueryProcess,
  color : Color
]

QueryReplyMessage ≜ [
  type  : {QueryReplyMessageType},
  src   : SlushQueryProcess,
  dst   : SlushLoopProcess,
  color : Color
]

TerminationMessage ≜ [
  type  : {TerminationMessageType},
  pid   : SlushLoopProcess
]

Message ≜
  QueryMessage
  ∪ QueryReplyMessage
  ∪ TerminationMessage

NoMessage ≜ CHOOSE m : m ∉ Message

TypeInvariant ≜
  ∧ pick ∈ [Node → Color ∪ {NoColor}]
  ∧ message ⊆ Message

PendingQueryMessage(pid) ≜ {
  m ∈ message :
    ∧ m.type = QueryMessageType
    ∧ m.dst = pid
}

PendingQueryReplyMessage(pid) ≜ {
  m ∈ message :
    ∧ m.type = QueryReplyMessageType
    ∧ m.dst = pid
}

Terminate ≜
  message = TerminationMessage

Pick(pid) ≜ pick[HostOf[pid]]

VARIABLES sampleSet, loopVariant

vars ≜ ⟨ pick, message, pc, sampleSet, loopVariant ⟩

ProcSet ≜ (SlushQueryProcess) ∪ (SlushLoopProcess) ∪ {"ClientRequest"}

Init ≜ (* Global variables *)
        ∧ pick = [node ∈ Node ↦ NoColor]
        ∧ message = {}
        (* Process SlushLoop *)
        ∧ sampleSet = [self ∈ SlushLoopProcess ↦ {}]
        ∧ loopVariant = [self ∈ SlushLoopProcess ↦ 0]
        ∧ pc = [self ∈ ProcSet ↦ CASE self ∈ SlushQueryProcess → "QueryReplyLoop"
                                        □ self ∈ SlushLoopProcess → "RequireColorAssignment"
                                        □ self = "ClientRequest" → "ClientRequestLoop"]

QueryReplyLoop(self) ≜ ∧ pc[self] = "QueryReplyLoop"
                       ∧ IF ¬Terminate
                              THEN ∧ pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
                              ELSE ∧ pc' = [pc EXCEPT ![self] = "Done"]
                       ∧ UNCHANGED ⟨ pick, message, sampleSet, loopVariant ⟩

WaitForQueryMessageOrTermination(self) ≜ ∧ pc[self] = "WaitForQueryMessageOrTermination"
                                         ∧ PendingQueryMessage(self) ≠ {} ∨ Terminate
                                         ∧ IF Terminate
                                                THEN ∧ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
                                                ELSE ∧ pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
                                         ∧ UNCHANGED ⟨ pick, message, 
                                                          sampleSet, 
                                                          loopVariant ⟩

RespondToQueryMessage(self) ≜ ∧ pc[self] = "RespondToQueryMessage"
                              ∧ ∃ msg ∈ PendingQueryMessage(self):
                                    LET color ≜ IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
                                      ∧ pick' = [pick EXCEPT ![HostOf[self]] = color]
                                      ∧ message' = (         (message \ {msg}) ∪
                                                     {[type  ↦ QueryReplyMessageType,
                                                     src     ↦ self,
                                                     dst     ↦ msg.src,
                                                     color   ↦ color]})
                              ∧ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
                              ∧ UNCHANGED ⟨ sampleSet, loopVariant ⟩

SlushQuery(self) ≜ QueryReplyLoop(self)
                       ∨ WaitForQueryMessageOrTermination(self)
                       ∨ RespondToQueryMessage(self)

RequireColorAssignment(self) ≜ ∧ pc[self] = "RequireColorAssignment"
                               ∧ Pick(self) ≠ NoColor
                               ∧ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
                               ∧ UNCHANGED ⟨ pick, message, sampleSet, 
                                                loopVariant ⟩

ExecuteSlushLoop(self) ≜ ∧ pc[self] = "ExecuteSlushLoop"
                         ∧ IF loopVariant[self] < SlushIterationCount
                                THEN ∧ pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
                                ELSE ∧ pc' = [pc EXCEPT ![self] = "SlushLoopTermination"]
                         ∧ UNCHANGED ⟨ pick, message, sampleSet, 
                                          loopVariant ⟩

QuerySampleSet(self) ≜ ∧ pc[self] = "QuerySampleSet"
                       ∧ ∃ possibleSampleSet ∈ LET
                                                      otherNodes ≜ Node \ {HostOf[self]}
                                                      otherQueryProcesses ≜ {pid ∈ SlushQueryProcess : HostOf[pid] ∈ otherNodes}
                                                    IN {pidSet ∈ SUBSET otherQueryProcesses : Cardinality(pidSet) = SampleSetSize}:
                             ∧ sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
                             ∧ message' = (         message ∪
                                            {[type  ↦ QueryMessageType,
                                            src     ↦ self,
                                            dst     ↦ pid,
                                            color   ↦ Pick(self)] :
                                              pid ∈ sampleSet'[self]})
                       ∧ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
                       ∧ UNCHANGED ⟨ pick, loopVariant ⟩

TallyQueryReplies(self) ≜ ∧ pc[self] = "TallyQueryReplies"
                          ∧ ∧ ∀ pid ∈ sampleSet[self] :
                                ∧ ∃ msg ∈ PendingQueryReplyMessage(self) :
                                  ∧ msg.src = pid
                          ∧ LET redTally ≜          Cardinality(
                                              {msg ∈ PendingQueryReplyMessage(self) :
                                                ∧ msg.src ∈ sampleSet[self]
                                                ∧ msg.color = Red}) IN
                                LET blueTally ≜           Cardinality(
                                                 {msg ∈ PendingQueryReplyMessage(self) :
                                                   ∧ msg.src ∈ sampleSet[self]
                                                   ∧ msg.color = Blue}) IN
                                  IF redTally ≥ PickFlipThreshold
                                     THEN ∧ pick' = [pick EXCEPT ![HostOf[self]] = Red]
                                     ELSE ∧ IF blueTally ≥ PickFlipThreshold
                                                THEN ∧ pick' = [pick EXCEPT ![HostOf[self]] = Blue]
                                                ELSE ∧ TRUE
                                                     ∧ pick' = pick
                          ∧ message' =          message \
                                         {msg ∈ message :
                                           ∧ msg.type = QueryReplyMessageType
                                           ∧ msg.src ∈ sampleSet[self]
                                           ∧ msg.dst = self}
                          ∧ sampleSet' = [sampleSet EXCEPT ![self] = {}]
                          ∧ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
                          ∧ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) ≜ ∧ pc[self] = "SlushLoopTermination"
                             ∧ message' = (                                 message ∪ {[
                                               type ↦ TerminationMessageType, pid ↦ self
                                             ]})
                             ∧ pc' = [pc EXCEPT ![self] = "Done"]
                             ∧ UNCHANGED ⟨ pick, sampleSet, loopVariant ⟩

SlushLoop(self) ≜ RequireColorAssignment(self) ∨ ExecuteSlushLoop(self)
                      ∨ QuerySampleSet(self) ∨ TallyQueryReplies(self)
                      ∨ SlushLoopTermination(self)

ClientRequestLoop ≜ ∧ pc["ClientRequest"] = "ClientRequestLoop"
                    ∧ IF ∃ n ∈ Node : pick[n] = NoColor
                           THEN ∧ pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
                           ELSE ∧ pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
                    ∧ UNCHANGED ⟨ pick, message, sampleSet, loopVariant ⟩

AssignColorToNode ≜ ∧ pc["ClientRequest"] = "AssignColorToNode"
                    ∧ ∃ node ∈ Node:
                          ∃ color ∈ Color:
                            IF pick[node] = NoColor
                               THEN ∧ pick' = [pick EXCEPT ![node] = color]
                               ELSE ∧ TRUE
                                    ∧ pick' = pick
                    ∧ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
                    ∧ UNCHANGED ⟨ message, sampleSet, loopVariant ⟩

ClientRequest ≜ ClientRequestLoop ∨ AssignColorToNode

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ≜ ∧ ∀ self ∈ ProcSet: pc[self] = "Done"
              ∧ UNCHANGED vars

Next ≜ ClientRequest
           ∨ (∃ self ∈ SlushQueryProcess: SlushQuery(self))
           ∨ (∃ self ∈ SlushLoopProcess: SlushLoop(self))
           ∨ Terminating

Spec ≜ Init ∧ □[Next]_vars

Termination ≜ ◇(∀ self ∈ ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================