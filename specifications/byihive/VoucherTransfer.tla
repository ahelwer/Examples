\* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
\*
\* Released under the terms of the Apache License 2.0
\* See: file LICENSE that came with this software for details.
\*
\* This file contains Intellectual Property that belongs to
\* Backyard Innovations Pte Ltd., Singapore.
\*
\* Authors: Santhosh Raju <santhosh@byisystems.com>
\*          Cherry G. Mathew <cherry@byisystems.com>
\*          Fransisca Andriani <sisca@byisystems.com>
\*
-------------------------- MODULE VoucherTransfer --------------------------

(***************************************************************************)
(* The description is based on the "Transfer" operation mentioned in RFC   *)
(* 3506. This specification describes the transfer of Voucher between two  *)
(* Holders. It is implemented over the Two-Phase Commit protocol, in which *)
(* a Voucher Transaction Provider (VTP) coordinates the "Source" Voucher   *)
(* Holders (SHs) to trade vouchers (Vs) to "Destination" Voucher Holders   *)
(* (DHs) described in the VoucherLifeCycle specification module. In this   *)
(* specification, SHs and DHs spontaneously issue Prepared messages. We    *)
(* ignore the Prepare messages that the VTP can send to the SHs and DHs.   *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an SHs and DHs *)
(* when it decides to abort. Such a message would cause the VTP to abort   *)
(* the transaction, an event represented here by the VTP spontaneously     *)
(* deciding to abort.                                                      *)
(*                                                                         *)
(* Note: The RFC does not differentiate between a Holder who is initiating *)
(* the transfer (i.e. the holder of the voucher) and the Holder who is     *)
(* receiving the voucher (i.e. the holder who would be the future owner of *)
(* this voucher). In order to make this distinction we have the "Source"   *)
(* Voucher Holders (SHs), a subset of Holders who would like to transfer   *)
(* an existing voucher they are "holding". We also have the "Destination"  *)
(* Voucher Holders (DHs), a subset of Holders who are "waiting" to receive *)
(* the transferred vouchers.                                               *)
(***************************************************************************)
CONSTANT
    V,             \* The set of Vouchers
    SH,            \* The set of "Source" Voucher Holders
    DH             \* The set of "Destination" Voucher Holders

VARIABLES
  vState,          \* vState[v] is the state of voucher v.
  vlcState,        \* vlcState[v] is the state of the voucher life cycle
                   \* machine.
  shState,         \* shState[sh] is the state of "source" voucher holder sh.
  dhState,         \* dhState[dh] is the state of "destination" voucher holder dh.
  vtpState,        \* The state of the voucher transaction provider.
  vtpTPrepared,    \* The set of SHs and DHs from which the VTP has received
                   \* "Prepared for Voucher Transfer" messages.
  msgs
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  For simplicity, we represent message passing with the    *)
    (* variable msgs whose value is the set of all messages that have been *)
    (* sent.  A message is sent by adding it to the set msgs.  An action   *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the presence of that message in  *)
    (* msgs.  For simplicity, messages are never removed from msgs.  This  *)
    (* allows a single message to be received by multiple receivers.       *)
    (* Receipt of the same message twice is therefore allowed; but in this *)
    (* particular protocol, that's not a problem.                          *)
    (***********************************************************************)

Messages ≜
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the SH indicated by the message's vsh field to the VTP.     *)
  (* Similar "Prepared" is also sent from DH indicated by message's vdh    *)
  (* field to the VTP. Messages of type "Transfer" and "Abort" are         *)
  (* broadcast by the VTPs, to be received by all SHs and DHs. The set     *)
  (* msgs contains just a single copy of such a message.                   *)
  (*************************************************************************)
  [type : {"Prepared"}, vsh : SH] ∪
  [type : {"Prepared"}, vdh : DH] ∪
  [type : {"Transfer", "Abort"}]

VTPTypeOK ≜
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  ∧ vState ∈ [V → {"valid"}]
  ∧ vlcState ∈ [V → {"working"}]
  ∧ shState ∈ [SH → {"holding", "prepared", "transferred", "aborted"}]
  ∧ dhState ∈ [DH → {"waiting", "prepared", "holding", "aborted"}]
  ∧ vtpState ∈ {"init", "done"}
  ∧ vtpTPrepared ⊆ (SH ∪ DH)
  ∧ msgs ⊆ Messages

VTPInit ≜
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ shState = [sh ∈ SH ↦ "holding"]
  ∧ dhState = [dh ∈ DH ↦ "waiting"]
  ∧ vtpState = "init"
  ∧ vtpTPrepared   = {}
  ∧ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the VTP's actions, the SHs' actions, then the DHs' actions.             *)
(***************************************************************************)
VTPRcvPrepared(sh,dh) ≜
  (*************************************************************************)
  (* The VTP receives a "Prepared" message from Source Voucher Holder sh   *)
  (* and the Destination Voucher Holder dh. We could add the additional    *)
  (* enabling condition sh,dh \not in vtpTPrepared, which disables the     *)
  (* action if the VTP has already received this message. But there is     *)
  (* no need, because in that case the action has no effect; it leaves the *)
  (* state unchanged.                                                      *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ vtpState = "init"
  ∧ [type ↦ "Prepared", vsh ↦ sh] ∈ msgs
  ∧ [type ↦ "Prepared", vdh ↦ dh] ∈ msgs
  ∧ vtpTPrepared' = vtpTPrepared ∪ {sh,dh}
  ∧ UNCHANGED ⟨vState, vlcState, shState, dhState, vtpState, msgs⟩

VTPTransfer(v) ≜
  (*************************************************************************)
  (* The VTP Transfers the voucher; enabled iff the VTP is in its          *)
  (* initial state and every SH and DH has sent a "Prepared" message.      *)
  (*************************************************************************)
  ∧ vState[v] = "valid"
  ∧ vlcState[v] = "working"
  ∧ vtpState = "init"
  ∧ vtpTPrepared = SH ∪ DH
  ∧ vtpState' = "done"
  ∧ msgs' = msgs ∪ {[type ↦ "Transfer"]}
  ∧ UNCHANGED ⟨shState, dhState, vState, vlcState, vtpTPrepared⟩

VTPAbort(v) ≜
  (*************************************************************************)
  (* The VTP spontaneously aborts the transaction.                         *)
  (*************************************************************************)
  ∧ vState[v] = "valid"
  ∧ vlcState[v] = "working"
  ∧ vtpState = "init"
  ∧ vtpState' = "done"
  ∧ msgs' = msgs ∪ {[type ↦ "Abort"]}
  ∧ UNCHANGED ⟨vState, vlcState, shState, dhState, vtpTPrepared⟩

SHPrepare(sh) ≜
  (*************************************************************************)
  (* Source Voucher holder sh prepares.                                    *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ shState[sh] = "holding"
  ∧ shState' = [shState EXCEPT ![sh] = "prepared"]
  ∧ msgs' = msgs ∪ {[type ↦ "Prepared", vsh ↦ sh]}
  ∧ UNCHANGED ⟨vState, vlcState, vtpState, dhState, vtpTPrepared⟩

SHChooseToAbort(sh) ≜
  (*************************************************************************)
  (* Source Voucher holder sh spontaneously decides to abort. As noted     *)
  (* above, sh does not send any message in our simplified spec.           *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ shState[sh] = "holding"
  ∧ shState' = [shState EXCEPT ![sh] = "aborted"]
  ∧ UNCHANGED ⟨vState, vlcState, vtpState, dhState, vtpTPrepared, msgs⟩

SHRcvTransferMsg(sh) ≜
  (*************************************************************************)
  (* Source Voucher holder sh is told by the VTP to Transfer.              *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ shState[sh] = "holding"
  ∧ [type ↦ "Transfer"] ∈ msgs
  ∧ shState' = [shState EXCEPT ![sh] = "transferred"]
  ∧ UNCHANGED ⟨vtpState, vlcState, vState, dhState, vtpTPrepared, msgs⟩

SHRcvAbortMsg(sh) ≜
  (*************************************************************************)
  (* Source Voucher holder sh is told by the VTP to abort.                 *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ shState[sh] = "holding"
  ∧ [type ↦ "Abort"] ∈ msgs
  ∧ shState' = [shState EXCEPT ![sh] = "aborted"]
  ∧ UNCHANGED ⟨vState, vlcState, vtpState, dhState, vtpTPrepared, msgs⟩

DHPrepare(dh) ≜
  (*************************************************************************)
  (* Destination Voucher holder dh prepares.                                         *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ dhState[dh] = "waiting"
  ∧ dhState' = [dhState EXCEPT ![dh] = "prepared"]
  ∧ msgs' = msgs ∪ {[type ↦ "Prepared", vdh ↦ dh]}
  ∧ UNCHANGED ⟨vState, vlcState, vtpState, shState, vtpTPrepared⟩

DHChooseToAbort(dh) ≜
  (*************************************************************************)
  (* Destination Voucher holder dh spontaneously decides to abort. As      *)
  (* noted above, dh does not send any message in our simplified spec.     *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ dhState[dh] = "waiting"
  ∧ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  ∧ UNCHANGED ⟨vState, vlcState, vtpState, shState, vtpTPrepared, msgs⟩

DHRcvTransferMsg(dh) ≜
  (*************************************************************************)
  (* Destination Voucher holder dh is told by the VTP to Transfer.         *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ dhState[dh] = "waiting"
  ∧ [type ↦ "Transfer"] ∈ msgs
  ∧ dhState' = [dhState EXCEPT ![dh] = "holding"]
  ∧ UNCHANGED ⟨vtpState, vState, vlcState, shState, vtpTPrepared, msgs⟩

DHRcvAbortMsg(dh) ≜
  (*************************************************************************)
  (* Destination Voucher holder dh is told by the VTP to abort.            *)
  (*************************************************************************)
  ∧ vState = [v ∈ V ↦ "valid"]
  ∧ vlcState = [v ∈ V ↦ "working"]
  ∧ dhState[dh] = "waiting"
  ∧ [type ↦ "Abort"] ∈ msgs
  ∧ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  ∧ UNCHANGED ⟨vState, vlcState, vtpState, shState, vtpTPrepared, msgs⟩

VTPNext ≜
  ∨ ∃ v ∈ V:
       VTPTransfer(v) ∨ VTPAbort(v)
  ∨ ∃ sh,dh ∈ SH ∪ DH:
       VTPRcvPrepared(sh,dh)
  ∨ ∃ sh ∈ SH:
       SHPrepare(sh) ∨ SHChooseToAbort(sh)
       ∨ SHRcvAbortMsg(sh) ∨ SHRcvTransferMsg(sh)
  ∨ ∃ dh ∈ DH:
       DHPrepare(dh) ∨ DHChooseToAbort(dh)
       ∨ DHRcvAbortMsg(dh) ∨ DHRcvTransferMsg(dh)
-----------------------------------------------------------------------------
VTPConsistent ≜
  (*************************************************************************)
  (* A state predicate asserting that a SH and an DH have not reached      *)
  (* conflicting decisions. It is an invariant of the specification.       *)
  (*************************************************************************)
  ∧ ∀ sh ∈ SH, dh ∈ DH :   ∧ ¬ ∧ shState[sh] = "transferred"
                               ∧ dhState[dh] = "aborted"
                           ∧ ¬ ∧ shState[sh] = "aborted"
                               ∧ dhState[dh] = "holding"
-----------------------------------------------------------------------------
VTPVars ≜ ⟨shState, dhState, vState, vlcState, vtpState, vtpTPrepared, msgs⟩

VTPSpec ≜ VTPInit ∧ □[VTPNext]_VTPVars
  (*************************************************************************)
  (* The complete spec of the a Voucher Transfer using Two-Phase Commit    *)
  (* protocol.                                                             *)
  (*************************************************************************)

THEOREM VTPSpec ⇒ □(VTPTypeOK ∧ VTPConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate VTPTypeOK /\ VTPConsistent is an          *)
  (* invariant of the specification VTPSpec. Invariance of this            *)
  (* conjunction is equivalent to invariance of both of the formulas       *)
  (* VTPTypeOK and VTPConsistent.                                          *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Voucher Transfer specification implements the    *)
(* Voucher Life Cycle specification of a voucher mentioned in module       *)
(* VoucherLifeCycle. The following statement imports all the definitions   *)
(* from module VoucherLifeCycle into the current module.                   *)
(***************************************************************************)
INSTANCE VoucherLifeCycle

THEOREM VTPSpec ⇒ VSpec
  (*************************************************************************)
  (* This theorem asserts that the specification VTPSpec of the Two-Phase  *)
  (* Commit protocol implements the specification VSpec of the             *)
  (* Voucher life cycle specification.                                     *)
  (*************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Jun 12 13:15:55 IST 2018 by Fox
\* Created Fri Mar 16 17:45:37 SGT 2018 by Fox