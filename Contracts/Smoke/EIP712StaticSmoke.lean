import Contracts.Common
import Compiler.Modules.Hashing
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Contracts.Smoke

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Yul
open Verity hiding pure bind

def permitTypeHash : Nat :=
  (keccakString "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)").val

def permitStaticHashArgs : List Expr :=
  [ Expr.literal permitTypeHash
  , Expr.param "owner"
  , Expr.param "spender"
  , Expr.param "value"
  , Expr.param "nonce"
  , Expr.param "deadline"
  ]

def permitStructHashStmt : Stmt :=
  Compiler.Modules.Hashing.eip712HashStruct
    "structHash" (Expr.literal permitTypeHash)
    [ Expr.param "owner"
    , Expr.param "spender"
    , Expr.param "value"
    , Expr.param "nonce"
    , Expr.param "deadline"
    ]

def permitDigestStmt : Stmt :=
  Compiler.Modules.Hashing.eip712Digest
    "digest" (Expr.param "domainSeparator") (Expr.localVar "structHash")

def permitStaticHashAndDigestStmts : List Stmt :=
  [permitStructHashStmt, permitDigestStmt]

def permitScope : List String :=
  ["domainSeparator", "owner", "spender", "value", "nonce", "deadline"]

def permitStaticStructHashLayoutCorrect : Prop :=
  (Compiler.Modules.Hashing.abiEncodeStaticWordsModule "structHash" 6).axioms =
    ["keccak256_memory_slice_matches_evm", "abi_standard_static_word_layout"] ∧
  (Compiler.Modules.Hashing.abiEncodeStaticWordsModule "structHash" 6).compile {}
      [ YulExpr.lit permitTypeHash
      , YulExpr.ident "owner"
      , YulExpr.ident "spender"
      , YulExpr.ident "value"
      , YulExpr.ident "nonce"
      , YulExpr.ident "deadline"
      ] =
    Except.ok (Compiler.Modules.Hashing.permitStructHashExpectedYul permitTypeHash)

def permitStaticDigestLayoutCorrect : Prop :=
  (Compiler.Modules.Hashing.eip712DigestModule "digest").axioms =
    ["keccak256_memory_slice_matches_evm", "eip712_digest_layout"] ∧
  (Compiler.Modules.Hashing.eip712DigestModule "digest").compile {}
      [YulExpr.ident "domainSeparator", YulExpr.ident "structHash"] =
    Except.ok Compiler.Modules.Hashing.eip712DigestExpectedYul

private theorem permitStaticHashAndDigest_supported :
    SupportedStmtList [] permitScope permitStaticHashAndDigestStmts := by
  change SupportedStmtList [] permitScope ([permitStructHashStmt] ++ [permitDigestStmt])
  apply SupportedStmtList.append
  · apply SupportedStmtList.pureHashingEcm
    · simp [ecmPureHashing, Compiler.Modules.Hashing.abiEncodeStaticWordsModule]
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames,
          permitScope, collectStmtBindNames,
          Compiler.Modules.Hashing.abiEncodeStaticWordsModule]
  · apply SupportedStmtList.pureHashingEcm
    · simp [ecmPureHashing, Compiler.Modules.Hashing.eip712DigestModule]
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl <;> constructor
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl <;>
        simp [FunctionBody.exprBoundNamesInScope, FunctionBody.exprBoundNames,
          stmtNextScope, permitScope, permitStructHashStmt,
          collectStmtBindNames,
          Compiler.Modules.Hashing.eip712HashStruct,
          Compiler.Modules.Hashing.abiEncodeStaticWords,
          Compiler.Modules.Hashing.abiEncodeStaticWordsModule]

theorem permitStaticHash_eip712Supported_and_digest_correct :
    SupportedStmtList [] permitScope permitStaticHashAndDigestStmts ∧
      permitStaticStructHashLayoutCorrect ∧
      permitStaticDigestLayoutCorrect := by
  constructor
  · exact permitStaticHashAndDigest_supported
  · constructor
    · constructor
      · rfl
      · exact Compiler.Modules.Hashing.abiEncodeStaticWordsModule_compile_permitStructHash_layout
          permitTypeHash
    · constructor
      · rfl
      · exact Compiler.Modules.Hashing.eip712DigestModule_compile_digest_layout

set_option linter.unusedVariables false in
verity_contract EIP712StaticSmoke where
  storage

  function recoverPermitSigner
      (domainSeparator : Bytes32, owner : Address, spender : Address,
       value : Uint256, nonce : Uint256, deadline : Uint256,
       v : Uint256, r : Bytes32, s : Bytes32) : Address := do
    let structHash ← ecmCall
      (fun resultVar => Compiler.Modules.Hashing.abiEncodeStaticWordsModule resultVar 6)
      [keccakString "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)",
       addressToWord owner, addressToWord spender, value, nonce, deadline]
    let digest ← ecmCall Compiler.Modules.Hashing.eip712DigestModule
      [domainSeparator, structHash]
    let signer ← ecrecover digest v r s
    return signer

example :
    EIP712StaticSmoke.recoverPermitSigner_modelBody =
      [ permitStructHashStmt
      , permitDigestStmt
      , Compiler.Modules.Precompiles.ecrecover
          "signer" (Expr.localVar "digest") (Expr.param "v") (Expr.param "r") (Expr.param "s")
      , Stmt.return (Expr.localVar "signer")
      ] := rfl

private def ecmMetadataAdversary :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ state => state.writeSlot 99 7
  result := fun site _ => .success
    [if site.name == (Compiler.Modules.Hashing.eip712DigestModule "result").summaryName &&
        site.kind == .staticcall then 1 else 0]
  gasUsed := fun _ _ => 0

example :
    let mod := Compiler.Modules.Hashing.eip712DigestModule "result"
    let out := (Contracts.ecmCallWords mod ecmMetadataAdversary []).run defaultState
    out.getValue? = some 1 ∧ out.getState.readSlot 99 = 0 := by
  decide

end Contracts.Smoke
