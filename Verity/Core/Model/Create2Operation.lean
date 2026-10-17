import Verity.Core.Model.Create2PhysicalMemory
import Verity.Core.Model.Create2Access
import Verity.Core.Model.CreationStorage

/-! Value-zero CREATE2 for the exact Midnight constructor, composed at the
opcode boundary. Context and warm accounts are mandatory actual inputs.
Unsupported constructor bytes fail closed only when execution reaches them;
collision, nonce overflow and depth failure do not inspect the constructor.
This is not yet the Source/Denote/IR execution-context integration. -/
namespace Verity.Core.Model.Create2Operation
open Verity Create2Entry Create2Accounts Create2Runtime Create2Callee
open Compiler.CompilationModel.DenoteMemory

structure Frame where
  world : ContractState
  context : Context
  warm : Create2Access.WarmAccounts

inductive Result where
  | exceptional (frame : Frame)
  | continued (value : Uint256) (frame : Frame)

/-- Recognize the complete actual byte string, not a predicted runtime/hash
or a supplied constructor certificate. No trailing byte is discarded. -/
def decode (code : ByteArray) : Except String ByteArray :=
  let payload : ByteArray := ⟨code.data.extract MidnightInitcode.header.size code.size⟩
  if code.data = (MidnightInitcode.initcode payload).data then .ok payload
  else .error "unsupported CREATE2 constructor: expected exact Midnight initcode prefix"

theorem decode_sound (code payload : ByteArray) (decoded : decode code = .ok payload) :
    code = MidnightInitcode.initcode payload := by
  dsimp only [decode] at decoded
  split at decoded
  · cases decoded
    apply ByteArray.ext
    assumption
  · contradiction

/-- Perform the nonce/reservation gates before decoding. Reservation is a pure
function; the computed outcome is committed once by the outer operation. -/
def enterCode (accounts : Accounts) (creator target : Nat) (code : ByteArray)
    (gas : Nat) : Except String EnteredResult :=
  if Create2NonceEntry.maxCreatorNonce < (accounts creator).nonce then
    .error "CREATE2 creator nonce exceeds uint64 account projection"
  else if (accounts creator).nonce = Create2NonceEntry.maxCreatorNonce then
    .ok { outcome := .failed accounts ByteArray.empty, gasLeft := gas }
  else match reserve accounts creator target with
    | .collision after => .ok { outcome := .failed after ByteArray.empty, gasLeft := 0 }
    | .reserved _ => do
        let payload ← decode code
        runEntered accounts creator target payload gas

def outcomeValue : Outcome → Uint256
  | .created target _ => Uint256.ofNat target
  | .failed _ _ => 0

/-- Complete caller preparation, exact two-hash EIP-1014 address, access update,
computed constructor/deposit and canonical persistent/account commit. -/
def run (before : Frame) (offset size salt : Uint256) : Except String Result := do
  let preparation ← prepare before.world.byteMemory before.context offset.val size.val
  match preparation with
  | .exceptional =>
      .ok (.exceptional { before with context := { before.context with gas := 0 } })
  | .depthFailure memory gasLeft =>
      let world := before.world.installPhysicalMemory memory
      .ok (.continued 0 { before with world := { world with returndata := [] }, context := { before.context with gas := gasLeft } })
  | .forwarded child =>
      let world := before.world.installPhysicalMemory child.memory
      let creator := world.thisAddress.val
      let nonce := (world.creationAccounts creator).nonce
      if Create2NonceEntry.maxCreatorNonce < nonce then
        .error "CREATE2 creator nonce exceeds uint64 account projection"
      else if nonce = Create2NonceEntry.maxCreatorNonce then
        .ok (.continued 0 { before with world := { world with returndata := [] }, context := { before.context with gas := completeGas child child.childGas } })
      else
        let code := Create2.physicalInitcodeBytes world offset.val size.val
        let target := (Create2.create2AddressFromPhysicalMemory world offset size salt world.thisAddress).val
        let warm := Create2Access.warm before.warm target
        let result ← enterCode world.creationAccounts creator target code child.childGas
        let committed ← CreationStorage.commit world result.outcome
        .ok (.continued (outcomeValue result.outcome)
          { world := committed, context := { before.context with gas := completeGas child result.gasLeft }, warm := warm })

/-- Same-caller rollback restores account/storage/memory/log and warm snapshots,
but retains the current gas. Restoring the old gas would invent a refund. -/
def rollback (snapshot current : Frame) : Frame :=
  { current with world := snapshot.world, warm := snapshot.warm }

theorem rollback_world (snapshot current : Frame) :
    (rollback snapshot current).world = snapshot.world := rfl

theorem rollback_warm (snapshot current : Frame) :
    (rollback snapshot current).warm = snapshot.warm := rfl

theorem rollback_gas (snapshot current : Frame) :
    (rollback snapshot current).context.gas = current.context.gas := rfl

theorem enterCode_overflow (accounts : Accounts) (creator target : Nat) (code : ByteArray)
    (gas : Nat) (overflow : (accounts creator).nonce = Create2NonceEntry.maxCreatorNonce) :
    enterCode accounts creator target code gas =
      .ok { outcome := .failed accounts ByteArray.empty, gasLeft := gas } := by
  simp only [enterCode, overflow, Nat.lt_irrefl, if_false, if_true]

theorem enterCode_collision (accounts : Accounts) (creator target : Nat) (code : ByteArray)
    (gas : Nat) (legal : (accounts creator).nonce < Create2NonceEntry.maxCreatorNonce)
    (after : Accounts) (collision : reserve accounts creator target = .collision after) :
    enterCode accounts creator target code gas =
      .ok { outcome := .failed after ByteArray.empty, gasLeft := 0 } := by
  have noInvalid : ¬ Create2NonceEntry.maxCreatorNonce < (accounts creator).nonce := by omega
  simp only [enterCode, noInvalid, Nat.ne_of_lt legal, if_false, collision]

theorem enterCode_reserved (accounts : Accounts) (creator target : Nat)
    (code payload : ByteArray) (gas : Nat)
    (legal : (accounts creator).nonce < Create2NonceEntry.maxCreatorNonce)
    (after : Accounts) (reserved : reserve accounts creator target = .reserved after)
    (decoded : decode code = .ok payload) :
    enterCode accounts creator target code gas = runEntered accounts creator target payload gas := by
  have noInvalid : ¬ Create2NonceEntry.maxCreatorNonce < (accounts creator).nonce := by omega
  simp only [enterCode, noInvalid, Nat.ne_of_lt legal, if_false, reserved, decoded]
  rfl

theorem run_exceptional (before : Frame) (offset size salt : Uint256)
    (exceptional : prepare before.world.byteMemory before.context offset.val size.val = .ok .exceptional) :
    run before offset size salt =
      .ok (.exceptional { before with context := { before.context with gas := 0 } }) := by
  simp only [run, exceptional]
  rfl

theorem run_depth_failure (before : Frame) (offset size salt : Uint256)
    (memory : Memory) (gasLeft : Nat)
    (failed : prepare before.world.byteMemory before.context offset.val size.val =
      .ok (.depthFailure memory gasLeft)) :
    run before offset size salt = .ok (.continued 0
      { before with world := { before.world.installPhysicalMemory memory with returndata := [] }, context := { before.context with gas := gasLeft } }) := by
  simp only [run, failed]
  rfl

theorem enterCode_self (accounts : Accounts) (creator : Nat) (code : ByteArray)
    (gas : Nat) (legal : (accounts creator).nonce < Create2NonceEntry.maxCreatorNonce) :
    enterCode accounts creator creator code gas =
      .ok { outcome := .failed (bumpCreator accounts creator) ByteArray.empty, gasLeft := 0 } :=
  enterCode_collision accounts creator creator code gas legal (bumpCreator accounts creator)
    (reserve_self_collision accounts creator)

theorem enterCode_frame (accounts : Accounts) (creator target query : Nat) (code : ByteArray)
    (gas : Nat) (result : EnteredResult) (executed : enterCode accounts creator target code gas = .ok result)
    (notCreator : query ≠ creator) (notTarget : query ≠ target) :
    result.outcome.accounts query = accounts query := by
  unfold enterCode at executed
  split at executed
  · contradiction
  · split at executed
    · cases executed; rfl
    · cases reservation : reserve accounts creator target with
      | collision after =>
          simp only [reservation, Except.ok.injEq] at executed
          cases executed
          have outside := reserve_frame accounts creator target query notCreator notTarget
          simpa only [reservation, Reservation.accounts, Outcome.accounts] using outside
      | reserved after =>
          simp only [reservation] at executed
          cases decoded : decode code with
          | error message =>
              simp only [decoded] at executed
              change Except.error message = Except.ok result at executed
              contradiction
          | ok payload =>
              simp only [decoded] at executed
              exact runEntered_frame accounts creator target query payload gas result executed notCreator notTarget

theorem run_nonce_overflow (before : Frame) (offset size salt : Uint256) (child : Forwarded)
    (prepared : prepare before.world.byteMemory before.context offset.val size.val = .ok (.forwarded child))
    (overflow : (before.world.creationAccounts before.world.thisAddress.val).nonce = Create2NonceEntry.maxCreatorNonce) :
    run before offset size salt = .ok (.continued 0
      { before with world := { before.world.installPhysicalMemory child.memory with returndata := [] }, context := { before.context with gas := completeGas child child.childGas } }) := by
  simp only [run, prepared]
  change (if Create2NonceEntry.maxCreatorNonce < (before.world.creationAccounts before.world.thisAddress.val).nonce then _ else _) = _
  simp only [ContractState.installPhysicalMemory, overflow, Nat.lt_irrefl, if_false, if_true]

end Verity.Core.Model.Create2Operation
