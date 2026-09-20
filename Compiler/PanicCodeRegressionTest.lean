import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Selectors
import Compiler.Proofs.IRGeneration.PanicPayloadIR
import Compiler.Proofs.YulGeneration.PanicPayloadBytes
import Compiler.TypedIRCompiler
import Compiler.TypedIRLowering

namespace Compiler.PanicCodeRegressionTest

open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Yul
open Verity.Core
open Verity.Core.Free

example : PanicCode.arithmeticOverflow.toNat = 0x11 := by rfl

example : PanicCode.divisionByZero.toNat = 0x12 := by rfl

example : (Stmt.panic .arithmeticOverflow).directMetadata.subexpressions = [] := by rfl

example : (Stmt.panic .arithmeticOverflow).directMetadata.termination = .alwaysTerminates := by rfl

example : (Stmt.controlFlow (Stmt.panic .divisionByZero)).mayRevert = true := by
  native_decide

def typedDivisionByZeroEvalRevertsWithCode : Bool :=
  match evalTStmt Inhabited.default (.panic .divisionByZero) with
  | .revert reason => reason == "Panic(18)"
  | _ => false

example : typedDivisionByZeroEvalRevertsWithCode = true := by native_decide

def typedOverflowPanicLowersDirectly : Bool :=
  match compileStmt [] [] [] .calldata [] false [] []
      (Stmt.panic .arithmeticOverflow) with
  | .ok [
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x4e487b71]
      ]),
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 0x11]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 36])
    ] => true
  | _ => false

example : typedOverflowPanicLowersDirectly = true := by native_decide

def typedDivisionByZeroPanicLowersDirectly : Bool :=
  match lowerTStmts [TStmt.panic .divisionByZero] with
  | [
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x4e487b71]
      ]),
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 0x12]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 36])
    ] => true
  | _ => false

example : typedDivisionByZeroPanicLowersDirectly = true := by native_decide

private def typedPanicSourceCompilerSpec : CompilationModel := {
  name := "TypedPanicSourceCompiler"
  fields := []
  constructor := none
  functions := [
    { name := "run"
      params := []
      returnType := none
      body := [Stmt.panic .arithmeticOverflow] }
  ]
}

def typedPanicSourceCompilerSupportsTypedPanic : Bool :=
  match compileFunctionNamed typedPanicSourceCompilerSpec "run" with
  | .ok block =>
      match block.body with
      | [TStmt.panic .arithmeticOverflow] => true
      | _ => false
  | .error _ => false

example : typedPanicSourceCompilerSupportsTypedPanic = true := by native_decide

private def rawPanicSourceCompilerSpec : CompilationModel := {
  name := "RawPanicSourceCompiler"
  fields := []
  constructor := none
  functions := [
    { name := "run"
      params := []
      returnType := none
      body := [Stmt.panicCode (Expr.literal 0x21)] }
  ]
}

def rawPanicSourceCompilerPreservesCode : Bool :=
  match compileFunctionNamed rawPanicSourceCompilerSpec "run" with
  | .ok block =>
      match block.body with
      | [TStmt.panicCode (TExpr.uintLit code)] => code == 0x21
      | _ => false
  | .error _ => false

example : rawPanicSourceCompilerPreservesCode = true := by native_decide

private def panicPayloadWithRevertRange (code offset size : Nat) : List YulStmt :=
  (solidityPanicPayload code).take 2 ++
    [YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit offset, YulExpr.lit size])]

-- Counterexamples characterizing the current proof boundary: the IR interpreter
-- does not observe revert-data offsets, lengths, or bytes. These checks
-- intentionally pass; they do not claim that malformed payloads are valid on
-- the EVM. Revisit them when the interpreter gains a revert-data observable.
example (fuel : Nat) (state : IRState) (code offset size : Nat) :
    execIRStmts (fuel + 4) state (panicPayloadWithRevertRange code offset size) =
      execIRStmts (fuel + 4) state (solidityPanicPayload code) := by
  rfl

-- Both canonical-payload theorems also establish their memory/revert result
-- for an empty revert, despite the emitted-AST checks above requiring 36 bytes.
example (fuel : Nat) (state : IRState) :
    execIRStmts (fuel + 4) state (panicPayloadWithRevertRange 0x11 0 0) =
      .revert { state with memory := fun o =>
        if o = 4 then 0x11 else if o = 0 then panicSelectorWord else state.memory o } := by
  exact execIRStmts_arithmeticOverflowPanicPayload fuel state

example (fuel : Nat) (state : IRState) :
    execIRStmts (fuel + 4) state (panicPayloadWithRevertRange 0x12 0 0) =
      .revert { state with memory := fun o =>
        if o = 4 then 0x12 else if o = 0 then panicSelectorWord else state.memory o } := by
  exact execIRStmts_divisionByZeroPanicPayload fuel state

private def expectedPanicBytesForTest (code : UInt8) : ByteArray :=
  ⟨#[0x4e, 0x48, 0x7b, 0x71] ++ Array.replicate 31 0 ++ #[code]⟩

private theorem observePanicPayloadWithRevertRange_eq
    (state : EvmYul.MachineState) (code offset size : Nat) :
    observePanicPayloadBytes state (panicPayloadWithRevertRange code offset size) =
      some (((state.mstore (EvmYul.UInt256.ofNat 0)
          (EvmYul.UInt256.ofNat (0x4e487b71 * 2 ^ 224))).mstore
            (EvmYul.UInt256.ofNat 4) (EvmYul.UInt256.ofNat code)).evmRevert
              (EvmYul.UInt256.ofNat offset) (EvmYul.UInt256.ofNat size)).H_return := by
  rfl

-- The byte-level observer must distinguish the canonical payload from an empty,
-- truncated, or shifted revert, unlike the abstract IR result above.
example :
    observePanicPayloadBytes Inhabited.default
        (solidityPanicPayload PanicCode.arithmeticOverflow.toNat) =
      some (expectedPanicBytesForTest 0x11) := by
  rw [observePanicPayloadBytes_arithmeticOverflow]
  have hBE : BE (EvmYul.UInt256.ofNat 0x11).toNat =
      (⟨#[0x11]⟩ : ByteArray) := by decide +kernel
  simp only [Backends.Panic.expectedPanicBytes, EvmYul.UInt256.toByteArray, hBE,
    expectedPanicBytesForTest]
  simp [ffi.ByteArray.zeroes, -ByteArray.size_data, ByteArray.size]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [USize.toNat_sub, USize.toNat_ofNat, hbits, ByteArray.data_append, ByteArray.ext_iff]

example :
    observePanicPayloadBytes Inhabited.default
        (solidityPanicPayload PanicCode.divisionByZero.toNat) =
      some (expectedPanicBytesForTest 0x12) := by
  rw [observePanicPayloadBytes_divisionByZero]
  have hBE : BE (EvmYul.UInt256.ofNat 0x12).toNat =
      (⟨#[0x12]⟩ : ByteArray) := by decide +kernel
  simp only [Backends.Panic.expectedPanicBytes, EvmYul.UInt256.toByteArray, hBE,
    expectedPanicBytesForTest]
  simp [ffi.ByteArray.zeroes, -ByteArray.size_data, ByteArray.size]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [USize.toNat_sub, USize.toNat_ofNat, hbits, ByteArray.data_append, ByteArray.ext_iff]

example : observePanicPayloadBytes Inhabited.default (panicPayloadWithRevertRange 0x11 0 0) =
      some ByteArray.empty := by
  rw [observePanicPayloadWithRevertRange_eq]
  simp only [EvmYul.MachineState.evmRevert, EvmYul.MachineState.evmReturn]
  have hZero (memory : ByteArray) : memory.readWithPadding 0 0 = ByteArray.empty := by
    simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, ffi.ByteArray.zeroes]
    rfl
  apply congrArg some
  exact hZero _

example : (observePanicPayloadBytes Inhabited.default (panicPayloadWithRevertRange 0x11 0 35)).map
      ByteArray.size = some 35 := by
  rw [observePanicPayloadWithRevertRange_eq]
  simp only [EvmYul.MachineState.evmRevert, EvmYul.MachineState.evmReturn, Option.map_some]
  have hSize (memory : ByteArray) : (memory.readWithPadding 0 35).size = 35 := by
    unfold ByteArray.readWithPadding
    simp only [show ¬ 35 ≥ 2^64 by norm_num, ↓reduceIte, ByteArray.size_append]
    have hRead : (memory.readWithoutPadding 0 35).size ≤ 35 := by
      unfold ByteArray.readWithoutPadding
      split <;> simp [ByteArray.size_extract]
    have hPadding (n : Nat) (hn : n ≤ 35) :
        ((OfNat.ofNat 35 : USize) - (OfNat.ofNat n : USize)).toNat = 35 - n := by
      rw [USize.toNat_sub, USize.toNat_ofNat, USize.toNat_ofNat]
      rcases System.Platform.numBits_eq with hbits | hbits
      · rw [hbits]
        have hnMod : n % 4294967296 = n := Nat.mod_eq_of_lt (by omega)
        rw [hnMod]
        omega
      · rw [hbits]
        have hnMod : n % 18446744073709551616 = n := Nat.mod_eq_of_lt (by omega)
        rw [hnMod]
        omega
    simp only [ffi.ByteArray.zeroes, ByteArray.size, Array.size_replicate]
    change (memory.readWithoutPadding 0 35).size +
      ((OfNat.ofNat 35 : USize) - (OfNat.ofNat (memory.readWithoutPadding 0 35).size)).toNat = 35
    rw [hPadding _ hRead]
    omega
  apply congrArg some
  exact hSize _

example : observePanicPayloadBytes Inhabited.default (panicPayloadWithRevertRange 0x11 1 36) =
    some (⟨#[0x48, 0x7b, 0x71] ++ Array.replicate 31 0 ++ #[0x11, 0]⟩ : ByteArray) := by
  rw [observePanicPayloadWithRevertRange_eq]
  simp only [EvmYul.MachineState.evmRevert, EvmYul.MachineState.evmReturn,
    EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord, EvmYul.writeBytes]
  change some ((((EvmYul.UInt256.ofNat 0x11).toByteArray.write 0
    ((EvmYul.UInt256.ofNat (0x4e487b71 * 2^224)).toByteArray.write 0 ByteArray.empty 0 32)
    4 32).readWithPadding 1 36)) = _
  have hBE : BE (EvmYul.UInt256.ofNat 0x11).toNat = (⟨#[0x11]⟩ : ByteArray) := by decide +kernel
  have hSelector : BE (EvmYul.UInt256.ofNat (0x4e487b71 * 2 ^ 224)).toNat =
      (⟨#[0x4e, 0x48, 0x7b, 0x71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
          0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ : ByteArray) := by decide +kernel
  simp only [EvmYul.UInt256.toByteArray, hBE, hSelector]
  rcases System.Platform.numBits_eq with hbits | hbits <;>
    simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
      ffi.ByteArray.zeroes, -ByteArray.size_data, ByteArray.size, USize.toNat_sub,
      USize.toNat_ofNat, hbits, ByteArray.data_append, ByteArray.data_copySlice,
      ByteArray.data_extract, ByteArray.ext_iff]
  all_goals decide +kernel

def panicMloadCachesCodeBeforePayloadStores : Bool :=
  match compileStmt [] [] [] .calldata [] false [] []
      (Stmt.panicCode (Expr.mload (Expr.literal 0))) with
  | .ok [YulStmt.block [
      YulStmt.let_ codeName (YulExpr.call "mload" [YulExpr.lit 0]),
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x4e487b71]
      ]),
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.ident payloadCodeName]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 36])
    ]] =>
      codeName == "__panic_code" && payloadCodeName == codeName
  | _ => false

example : panicMloadCachesCodeBeforePayloadStores = true := by native_decide

def rawTypedIRPanicMappingReadCachesCodeBeforePayloadStores : Bool :=
  match lowerTStmts [TStmt.panicCode (TExpr.getMapping 0 TExpr.sender)] with
  | [YulStmt.block [
      YulStmt.let_ codeName
        (YulExpr.call "sload" [
          YulExpr.call "mappingSlot" [YulExpr.lit 0, YulExpr.call "caller" []]
        ]),
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex 0x4e487b71]
      ]),
      YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.ident payloadCodeName]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 36])
    ]] =>
      codeName == "__panic_code" && payloadCodeName == codeName
  | _ => false

example : rawTypedIRPanicMappingReadCachesCodeBeforePayloadStores = true := by native_decide

private def checkedArithmeticHelpersContract : Compiler.IRContract :=
  { name := "PanicRewriteRegression"
    deploy := []
    functions := []
    usesMapping := false
    internalFunctions := [
      checkedAddUint256Helper,
      checkedSubUint256Helper,
      checkedMulUint256Helper,
      checkedDivUint256Helper,
      panicError0x11Helper,
      panicError0x12Helper
    ] }

private def optimizeCheckedArithmeticRuntime (stmts : List YulStmt) : List YulStmt :=
  (Compiler.CodegenCommon.optimizeCheckedArithmeticObjectIfAvailable
      checkedArithmeticHelpersContract
      { name := "PanicRewriteRegression"
        deployCode := []
        runtimeCode := checkedArithmeticHelpersContract.internalFunctions ++ stmts }).runtimeCode.drop
    checkedArithmeticHelpersContract.internalFunctions.length

def mixedTypedAndRawPanicRewritesOnlyTyped : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let failCond := YulExpr.call "lt" [YulExpr.call "add" [lhs, rhs], lhs]
  let typedPair := [
    YulStmt.if_ failCond (solidityPanicPayload 0x11),
    YulStmt.let_ "typedResult" (YulExpr.call "add" [lhs, rhs])
  ]
  let rawGuard :=
    YulStmt.if_ failCond [YulStmt.block (
      YulStmt.let_ "__panic_code" (YulExpr.lit 0x11) ::
        solidityPanicPayloadExpr (YulExpr.ident "__panic_code"))]
  let rawPair := [
    rawGuard,
    YulStmt.let_ "rawResult" (YulExpr.call "add" [lhs, rhs])
  ]
  match optimizeCheckedArithmeticRuntime (typedPair ++ rawPair) with
  | [ YulStmt.let_ "typedResult" (YulExpr.call helperName [typedLhs, typedRhs]),
      rawGuardActual,
      YulStmt.let_ "rawResult" (YulExpr.call "add" [rawLhs, rawRhs]) ] =>
      helperName == checkedAddUint256HelperName &&
        typedLhs == lhs && typedRhs == rhs &&
        rawGuardActual == rawGuard && rawLhs == lhs && rawRhs == rhs
  | _ => false

example : mixedTypedAndRawPanicRewritesOnlyTyped = true := by native_decide

-- The CLI's --module boundary accepts a module's `spec : CompilationModel`.
-- Start at that source-model boundary, not at a hand-built Yul object. The
-- compiler must validate the model and insert arithmetic helpers itself.
private def sideEffectfulArithmeticSpec : CompilationModel := {
  name := "SideEffectfulArithmetic"
  fields := [{ name := "counter", ty := .uint256 }]
  constructor := none
  functions := [
    { name := "bump", params := [], returnType := some .uint256,
      isInternal := true,
      body := [
        .letVar "next" (.add (.storage "counter") (.literal 1)),
        .setStorage "counter" (.localVar "next"),
        .return (.localVar "next") ] },
    { name := "run", params := [], returnType := some .uint256,
      body := [
        .ite (.lt (.add (.internalCall "bump" []) (.literal 2))
          (.internalCall "bump" [])) [.panic .arithmeticOverflow] [],
        .letVar "result" (.add (.internalCall "bump" []) (.literal 2)),
        .return (.localVar "result") ] }
  ] }

private partial def countBumpCallsExpr : YulExpr → Nat
  | .call name args =>
      (if name == "internal_bump" then 1 else 0) +
        (args.map countBumpCallsExpr).sum
  | _ => 0

private partial def countBumpCallsStmt : YulStmt → Nat
  | .let_ _ value | .letMany _ value | .assign _ value | .exprStmt value =>
      countBumpCallsExpr value
  | .if_ cond body => countBumpCallsExpr cond + (body.map countBumpCallsStmt).sum
  | .for_ init cond post body =>
      countBumpCallsExpr cond + ((init ++ post ++ body).map countBumpCallsStmt).sum
  | .switch value cases fallback =>
      countBumpCallsExpr value +
        (cases.map (fun (_, body) => (body.map countBumpCallsStmt).sum)).sum +
        ((fallback.getD []).map countBumpCallsStmt).sum
  | .block body | .funcDef _ _ _ body => (body.map countBumpCallsStmt).sum
  | .comment _ | .leave => 0

-- Count syntactic calls, not EVM executions. In this straight-line fixture,
-- all three calls execute on the non-reverting path and each updates storage.
def compiledSideEffectfulArithmeticCallCounts : Except String (Nat × Nat) := do
  let contract ← compile sideEffectfulArithmeticSpec
    [Compiler.keccak256_first_4_bytes "run()"]
  unless contract.internalFunctions.any (fun stmt => match stmt with
      | .funcDef name _ _ _ => name == checkedAddUint256HelperName
      | _ => false) do
    throw "Expected compilation to insert the checked-add helper"
  let before := Compiler.emitYul contract
  let (after, _) := Compiler.emitYulWithOptionsReport contract {}
  pure ((before.runtimeCode.map countBumpCallsStmt).sum,
    (after.runtimeCode.map countBumpCallsStmt).sum)

-- Establish successful validation/lowering and the independently expected
-- three calls before testing that production emission preserves them.
example : compiledSideEffectfulArithmeticCallCounts.map Prod.fst = .ok 3 := by
  native_decide

example : compiledSideEffectfulArithmeticCallCounts.map Prod.snd = .ok 3 := by
  native_decide

-- Independent input patterns for each checked-arithmetic rewrite. Exercise
-- both operand positions: even division must not move a call past its guard.
private def arithmeticRewriteCases (a b : YulExpr) :
    List (List YulStmt × YulStmt) :=
  let cases := [
    ("add", checkedAddUint256HelperName, 0x11,
      YulExpr.call "lt" [.call "add" [a, b], a]),
    ("sub", checkedSubUint256HelperName, 0x11,
      YulExpr.call "lt" [a, b]),
    ("mul", checkedMulUint256HelperName, 0x11,
      YulExpr.call "iszero" [.call "or" [
        .call "iszero" [.call "iszero" [.call "eq" [b, .lit 0]]],
        .call "iszero" [.call "iszero" [.call "eq" [
          .call "div" [.call "mul" [a, b], b], a]]]]]),
    ("div", checkedDivUint256HelperName, 0x12,
      YulExpr.call "eq" [b, .lit 0])]
  cases.map fun (op, helper, code, cond) =>
    ([.if_ cond (solidityPanicPayload code), .let_ "result" (.call op [a, b])],
      .let_ "result" (.call helper [a, b]))

def checkedArithmeticSimpleOperandsStillRewrite : Bool :=
  let operands := [YulExpr.ident "value", .lit 2, .hex 3]
  operands.all fun a => operands.all fun b =>
    (arithmeticRewriteCases a b).all fun (input, expected) =>
      optimizeCheckedArithmeticRuntime input == [expected]

example : checkedArithmeticSimpleOperandsStillRewrite = true := by native_decide

def checkedArithmeticCallOperandsRemainUnchanged : Bool :=
  let operands := [
    YulExpr.call "internal_bump" [],
    .call "sload" [.lit 0],
    .call "add" [.call "internal_bump" [], .lit 1]]
  operands.all fun operand =>
    [(operand, YulExpr.ident "rhs"), (YulExpr.ident "lhs", operand)].all fun (a, b) =>
      (arithmeticRewriteCases a b).all fun (input, _) =>
        optimizeCheckedArithmeticRuntime input == input

example : checkedArithmeticCallOperandsRemainUnchanged = true := by native_decide

def yulOptimizerStandaloneTypedPanicDoesNotRewrite : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let failCond := YulExpr.call "lt" [YulExpr.call "add" [lhs, rhs], lhs]
  let stmts := [YulStmt.if_ failCond (solidityPanicPayload 0x11)]
  optimizeCheckedArithmeticRuntime stmts == stmts

example : yulOptimizerStandaloneTypedPanicDoesNotRewrite = true := by native_decide

def yulOptimizerReversedSubtractionGuardDoesNotRewrite : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let stmts := [
    YulStmt.if_ (YulExpr.call "lt" [rhs, lhs]) (solidityPanicPayload 0x11),
    YulStmt.let_ "result" (YulExpr.call "sub" [lhs, rhs])]
  optimizeCheckedArithmeticRuntime stmts == stmts

example : yulOptimizerReversedSubtractionGuardDoesNotRewrite = true := by native_decide

def yulOptimizerWrongSubtractionPanicCodeDoesNotRewrite : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let stmts := [
    YulStmt.if_ (YulExpr.call "lt" [lhs, rhs]) (solidityPanicPayload 0x12),
    YulStmt.let_ "result" (YulExpr.call "sub" [lhs, rhs])]
  optimizeCheckedArithmeticRuntime stmts == stmts

example : yulOptimizerWrongSubtractionPanicCodeDoesNotRewrite = true := by native_decide

def yulOptimizerMismatchedSubtractionOperandsDoNotRewrite : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let other := YulExpr.ident "other"
  let stmts := [
    YulStmt.if_ (YulExpr.call "lt" [lhs, rhs]) (solidityPanicPayload 0x11),
    YulStmt.let_ "result" (YulExpr.call "sub" [lhs, other])]
  optimizeCheckedArithmeticRuntime stmts == stmts

example : yulOptimizerMismatchedSubtractionOperandsDoNotRewrite = true := by native_decide

def yulOptimizerRawArithmeticLookalikeDoesNotRewrite : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let failCond := YulExpr.call "lt" [YulExpr.call "add" [lhs, rhs], lhs]
  let rawBody := [YulStmt.block (
    YulStmt.let_ "__panic_code" (YulExpr.lit 0x11) ::
      solidityPanicPayloadExpr (YulExpr.ident "__panic_code"))]
  let stmts := [
    YulStmt.if_ failCond rawBody,
    YulStmt.let_ "result" (YulExpr.call "add" [lhs, rhs])]
  optimizeCheckedArithmeticRuntime stmts == stmts

example : yulOptimizerRawArithmeticLookalikeDoesNotRewrite = true := by native_decide

def unsafeYulArithmeticPairRemainsOpaque : Bool :=
  let lhs := YulExpr.ident "lhs"
  let rhs := YulExpr.ident "rhs"
  let failCond := YulExpr.call "lt" [YulExpr.call "add" [lhs, rhs], lhs]
  let rawPair := [
    YulStmt.if_ failCond (solidityPanicPayload 0x11),
    YulStmt.let_ "result" (YulExpr.call "add" [lhs, rhs])]
  let fragment : UnsafeYulFragment := {
    label := "unsafe_arithmetic_pair"
    stmts := rawPair
    obligations := [] }
  match compileStmt [] [] [] .calldata [] false [] [] (Stmt.unsafeYul fragment) with
  | .ok lowered => optimizeCheckedArithmeticRuntime lowered == lowered
  | .error _ => false

example : unsafeYulArithmeticPairRemainsOpaque = true := by native_decide

private def sideEffectingEcmLookalike : Compiler.ECM.ExternalCallModule where
  name := "sideEffectingEcmLookalike"
  numArgs := 0
  resultVars := ["result"]
  writesState := true
  readsState := true
  compile := fun _ctx _args =>
    let lhs := YulExpr.call "bump" []
    let rhs := YulExpr.lit 2
    let failCond := YulExpr.call "lt" [YulExpr.call "add" [lhs, rhs], lhs]
    pure [
      YulStmt.if_ failCond (solidityPanicPayload 0x11),
      YulStmt.let_ "result" (YulExpr.call "add" [lhs, rhs])
    ]

def ecmCallOperandsRemainUnchanged : Bool :=
  match compileStmt [] [] [] .calldata [] false [] []
      (Stmt.ecm sideEffectingEcmLookalike []) with
  | .ok lowered => optimizeCheckedArithmeticRuntime lowered == lowered
  | .error _ => false

example : ecmCallOperandsRemainUnchanged = true := by native_decide

private def arithmeticEcm (stmts : List YulStmt) : Compiler.ECM.ExternalCallModule where
  name := "arithmeticEcm"
  numArgs := 0
  resultVars := ["result"]
  writesState := false
  readsState := false
  compile := fun _ _ => pure stmts

-- Exercise actual ECM lowering before the production object optimizer.
def ecmSimpleArithmeticRewritesAutomatically : Bool :=
  (arithmeticRewriteCases (.ident "lhs") (.lit 2)).all fun (input, expected) =>
    match compileStmt [] [] [] .calldata [] false [] [] (.ecm (arithmeticEcm input) []) with
    | .ok lowered =>
      match optimizeCheckedArithmeticRuntime lowered with
      | [.comment _, actual, .comment _] => actual == expected
      | _ => false
    | .error _ => false

example : ecmSimpleArithmeticRewritesAutomatically = true := by native_decide

private def optimizeObjectSections (deploy runtime : List YulStmt) : YulObject :=
  Compiler.CodegenCommon.optimizeCheckedArithmeticObjectIfAvailable
    checkedArithmeticHelpersContract
    { name := "HelperValidation", deployCode := deploy, runtimeCode := runtime }

def checkedArithmeticRequiresActualCanonicalHelpers : Bool :=
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, _) =>
    let helpers := checkedArithmeticHelpersContract.internalFunctions
    let invalidHelpers := [[], helpers.drop 1, helpers.take 4,
      helpers ++ [checkedAddUint256Helper],
      .funcDef checkedAddUint256HelperName ["x", "y"] ["sum"] [] :: helpers.drop 1]
    invalidHelpers.all fun definitions =>
      let code := definitions ++ input
      let optimized := optimizeObjectSections code code
      optimized.runtimeCode == code && optimized.deployCode == code

example : checkedArithmeticRequiresActualCanonicalHelpers = true := by native_decide

def checkedArithmeticRejectsHelperShadowing : Bool :=
  let helpers := checkedArithmeticHelpersContract.internalFunctions
  let conflicts := [
    YulStmt.block [.funcDef checkedAddUint256HelperName [] [] []],
    .let_ panicError0x11HelperName (.lit 0),
    .letMany [checkedDivUint256HelperName] (.lit 0),
    .funcDef "f" [checkedSubUint256HelperName] [] [],
    .funcDef "g" [] [panicError0x12HelperName] []]
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, _) =>
    conflicts.all fun conflict =>
      let code := helpers ++ [conflict] ++ input
      (optimizeObjectSections [] code).runtimeCode == code

example : checkedArithmeticRejectsHelperShadowing = true := by native_decide

def checkedArithmeticValidatesSectionsIndependently : Bool :=
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, expected) =>
    let helpers := checkedArithmeticHelpersContract.internalFunctions
    let first := optimizeObjectSections input (helpers ++ input)
    let second := optimizeObjectSections (helpers ++ input) input
    first.deployCode == input && first.runtimeCode == helpers ++ [expected] &&
      second.deployCode == helpers ++ [expected] && second.runtimeCode == input

example : checkedArithmeticValidatesSectionsIndependently = true := by native_decide

def checkedArithmeticMalformedRegionsFailClosed : Bool :=
  let beginEcm := YulStmt.comment StatementRegions.ecmBeginMarker
  let endEcm := YulStmt.comment StatementRegions.ecmEndMarker
  let beginUnsafe := YulStmt.comment UnsafeYulFragment.beginMarker
  let endUnsafe := YulStmt.comment UnsafeYulFragment.endMarker
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, _) =>
    [input ++ [beginEcm], [endEcm] ++ input,
      [beginEcm, beginUnsafe, endEcm, endUnsafe] ++ input,
      [YulStmt.block [beginEcm]] ++ input,
      input ++ [beginUnsafe]].all fun code =>
        optimizeCheckedArithmeticRuntime code == code

example : checkedArithmeticMalformedRegionsFailClosed = true := by native_decide

def ecmReservedMarkersRemainOpaque : Bool :=
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, _) =>
    [YulStmt.comment StatementRegions.ecmBeginMarker,
      .block [.comment StatementRegions.ecmEndMarker]].all fun forged =>
      match compileStmt [] [] [] .calldata [] false [] []
          (.ecm (arithmeticEcm (forged :: input)) []) with
      | .ok lowered => optimizeCheckedArithmeticRuntime lowered == lowered
      | .error _ => false

example : ecmReservedMarkersRemainOpaque = true := by native_decide

def checkedArithmeticRespectsRegionBoundaries : Bool :=
  let beginEcm := YulStmt.comment StatementRegions.ecmBeginMarker
  let endEcm := YulStmt.comment StatementRegions.ecmEndMarker
  let beginUnsafe := YulStmt.comment UnsafeYulFragment.beginMarker
  let endUnsafe := YulStmt.comment UnsafeYulFragment.endMarker
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, expected) =>
    match input with
    | [guard, binding] =>
      let splitPairs := [
        [guard, beginEcm, binding, endEcm],
        [beginEcm, guard, endEcm, binding],
        [beginEcm, guard, endEcm, beginEcm, binding, endEcm]]
      let nested := [beginEcm, beginUnsafe] ++ input ++ [endUnsafe] ++ input ++ [endEcm]
      splitPairs.all (fun code => optimizeCheckedArithmeticRuntime code == code) &&
        optimizeCheckedArithmeticRuntime nested ==
          [beginEcm, beginUnsafe] ++ input ++ [endUnsafe, expected, endEcm]
    | _ => false

example : checkedArithmeticRespectsRegionBoundaries = true := by native_decide

def ecmArithmeticRewritesNestedBodies : Bool :=
  (arithmeticRewriteCases (.ident "lhs") (.ident "rhs")).all fun (input, expected) =>
    let containers : List (List YulStmt → YulStmt) := [
      YulStmt.block, YulStmt.if_ (.lit 1), YulStmt.funcDef "f" [] [],
      fun body => .for_ body (.lit 0) body body,
      fun body => .switch (.lit 0) [(0, body)] (some body)]
    containers.all fun wrap =>
      match compileStmt [] [] [] .calldata [] false [] []
          (.ecm (arithmeticEcm [wrap input]) []) with
      | .ok lowered =>
        match optimizeCheckedArithmeticRuntime lowered with
        | [.comment _, actual, .comment _] => actual == wrap [expected]
        | _ => false
      | .error _ => false

example : ecmArithmeticRewritesNestedBodies = true := by native_decide

private def compiledEcmArithmeticSpec (withTypedPair : Bool) : CompilationModel :=
  let lhs := Expr.localVar "lhs"
  let rhs := Expr.literal 2
  let typedPair : List Stmt := [
    .ite (.lt (.add lhs rhs) lhs) [.panic .arithmeticOverflow] [],
    .letVar "typedResult" (.add lhs rhs)]
  { name := "CompiledEcmArithmetic"
    fields := []
    constructor := none
    functions := [
      { name := "run", params := [], returnType := some .uint256,
        body := [.letVar "lhs" (.literal 7)] ++
          (if withTypedPair then typedPair else []) ++ [
            .ecm (arithmeticEcm [
              .if_ (.call "lt" [.call "add" [.ident "lhs", .lit 2], .ident "lhs"])
                (solidityPanicPayload 0x11),
              .let_ "result" (.call "add" [.ident "lhs", .lit 2])]) [],
            .return (.localVar "result")] }] }

-- Real source-model entry: validation, helper insertion, ECM lowering, then emission.
def compiledEcmArithmeticOptimizesWhenHelpersExist : Except String Bool := do
  let contract ← compile (compiledEcmArithmeticSpec true)
    [Compiler.keccak256_first_4_bytes "run()"]
  let before := Compiler.emitYul contract
  let after := Compiler.emitYulWithOptions contract {}
  let expected := YulStmt.let_ "result"
    (.call "checked_add_t_uint256" [.ident "lhs", .lit 2])
  let absent := fun code => StatementRegions.allStatementLists
    (fun body => !body.contains expected) code
  pure (absent before.runtimeCode && !absent after.runtimeCode)

example : compiledEcmArithmeticOptimizesWhenHelpersExist = .ok true := by native_decide

def compiledEcmAloneDoesNotInsertHelpers : Except String Bool := do
  let contract ← compile (compiledEcmArithmeticSpec false)
    [Compiler.keccak256_first_4_bytes "run()"]
  let before := Compiler.emitYul contract
  let after := Compiler.emitYulWithOptions contract {}
  pure (before.runtimeCode == after.runtimeCode &&
    !contract.internalFunctions.contains checkedAddUint256Helper)

example : compiledEcmAloneDoesNotInsertHelpers = .ok true := by native_decide

end Compiler.PanicCodeRegressionTest
