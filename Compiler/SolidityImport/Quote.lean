import Lean
import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.Report

/-!
Term syntax for the `CompilationModel` values the importer builds.

The importer lowers Solidity to ordinary `CompilationModel` values and quotes
them here, so the elaborated definitions are the same terms a user would write.
Only the fragment the importer emits is quoted; anything else is an internal
error rather than a silently dropped field. `Stmt.ecm` holds functions and
cannot be quoted at all.
-/

open Lean

namespace Compiler.CompilationModel.SolidityImport

variable {m : Type → Type} [Monad m] [MonadQuotation m] [MonadError m]

private def list (xs : List Term) : m Term := `([$(xs.toArray),*])

private def optNat : Option Nat → m Term
  | none => `(none)
  | some n => `(some $(quote n))

partial def quoteExpr : Expr → m Term
  | .literal n => `(Compiler.CompilationModel.Expr.literal $(quote n))
  | .localVar x => `(Compiler.CompilationModel.Expr.localVar $(quote x))
  | .param x => `(Compiler.CompilationModel.Expr.param $(quote x))
  | .blockTimestamp => `(Compiler.CompilationModel.Expr.blockTimestamp)
  | .blockNumber => `(Compiler.CompilationModel.Expr.blockNumber)
  | .chainid => `(Compiler.CompilationModel.Expr.chainid)
  | .caller => `(Compiler.CompilationModel.Expr.caller)
  | .contractAddress => `(Compiler.CompilationModel.Expr.contractAddress)
  | .structMember f k x => do
      `(Compiler.CompilationModel.Expr.structMember $(quote f) $(← quoteExpr k) $(quote x))
  | .structMember2 f k1 k2 x => do
      `(Compiler.CompilationModel.Expr.structMember2 $(quote f) $(← quoteExpr k1) $(← quoteExpr k2) $(quote x))
  | .add a b => do `(Compiler.CompilationModel.Expr.add $(← quoteExpr a) $(← quoteExpr b))
  | .sub a b => do `(Compiler.CompilationModel.Expr.sub $(← quoteExpr a) $(← quoteExpr b))
  | .mul a b => do `(Compiler.CompilationModel.Expr.mul $(← quoteExpr a) $(← quoteExpr b))
  | .div a b => do `(Compiler.CompilationModel.Expr.div $(← quoteExpr a) $(← quoteExpr b))
  | .bitAnd a b => do `(Compiler.CompilationModel.Expr.bitAnd $(← quoteExpr a) $(← quoteExpr b))
  | .bitXor a b => do `(Compiler.CompilationModel.Expr.bitXor $(← quoteExpr a) $(← quoteExpr b))
  | .eq a b => do `(Compiler.CompilationModel.Expr.eq $(← quoteExpr a) $(← quoteExpr b))
  | .lt a b => do `(Compiler.CompilationModel.Expr.lt $(← quoteExpr a) $(← quoteExpr b))
  | .gt a b => do `(Compiler.CompilationModel.Expr.gt $(← quoteExpr a) $(← quoteExpr b))
  | .le a b => do `(Compiler.CompilationModel.Expr.le $(← quoteExpr a) $(← quoteExpr b))
  | .ge a b => do `(Compiler.CompilationModel.Expr.ge $(← quoteExpr a) $(← quoteExpr b))
  | .logicalNot a => do `(Compiler.CompilationModel.Expr.logicalNot $(← quoteExpr a))
  | e => throwError "internal: the importer cannot quote {repr e}"

private def quotePanic : Verity.Core.PanicCode → m Term
  | .arithmeticOverflow => `(Verity.Core.PanicCode.arithmeticOverflow)
  | .divisionByZero => `(Verity.Core.PanicCode.divisionByZero)

partial def quoteStmt : Stmt → m Term
  | .letVar x v => do `(Compiler.CompilationModel.Stmt.letVar $(quote x) $(← quoteExpr v))
  | .assignVar x v => do `(Compiler.CompilationModel.Stmt.assignVar $(quote x) $(← quoteExpr v))
  | .ite c t e => do
      `(Compiler.CompilationModel.Stmt.ite $(← quoteExpr c)
        $(← list (← t.mapM quoteStmt)) $(← list (← e.mapM quoteStmt)))
  | .panic code => do `(Compiler.CompilationModel.Stmt.panic $(← quotePanic code))
  | .returnValues vs => do
      `(Compiler.CompilationModel.Stmt.returnValues $(← list (← vs.mapM quoteExpr)))
  | _ => throwError "internal: the importer cannot quote this statement"

private def quoteKey : MappingKeyType → m Term
  | .bytes32 => `(Compiler.CompilationModel.MappingKeyType.bytes32)
  | .address => `(Compiler.CompilationModel.MappingKeyType.address)
  | .uint256 => `(Compiler.CompilationModel.MappingKeyType.uint256)

private def quoteMember (s : StructMember) : m Term := do
  let ty ← match s.ty with
    | .uint256 => `(Compiler.CompilationModel.StructMemberType.uint256)
    | .uint16 => `(Compiler.CompilationModel.StructMemberType.uint16)
    | t => throwError "internal: the importer cannot quote {repr t}"
  let packed ← match s.packed with
    | none => `(none)
    | some p => `(some ({ offset := $(quote p.offset), width := $(quote p.width) } :
        Compiler.CompilationModel.PackedBits))
  `(({ name := $(quote s.name), ty := $ty, wordOffset := $(quote s.wordOffset), packed := $packed } :
      Compiler.CompilationModel.StructMember))

def quoteField (f : Field) : m Term := do
  unless !f.isTransient && f.packedBits.isNone && f.aliasSlots.isEmpty do
    throwError "internal: field {f.name} has settings the importer does not emit"
  let ty ← match f.ty with
    | .mappingStruct k ms => do
        `(Compiler.CompilationModel.FieldType.mappingStruct $(← quoteKey k) $(← list (← ms.mapM quoteMember)))
    | .mappingStruct2 k1 k2 ms => do
        `(Compiler.CompilationModel.FieldType.mappingStruct2 $(← quoteKey k1) $(← quoteKey k2)
          $(← list (← ms.mapM quoteMember)))
    | t => throwError "internal: the importer cannot quote {repr t}"
  `(({ name := $(quote f.name), ty := $ty, slot := $(← optNat f.slot) } : Compiler.CompilationModel.Field))

def quoteParamType : ParamType → m Term
  | .uint256 => `(Compiler.CompilationModel.ParamType.uint256)
  | .address => `(Compiler.CompilationModel.ParamType.address)
  | .bytes32 => `(Compiler.CompilationModel.ParamType.bytes32)
  | .bool => `(Compiler.CompilationModel.ParamType.bool)
  | .uintN n => `(Compiler.CompilationModel.ParamType.uintN $(quote n))
  | t => throwError "internal: the importer cannot quote {repr t}"

/-- Quote a function built by the importer. Only the fields it sets are
emitted; `quoteModel` callers check the round trip against the value. -/
def quoteFunction (f : FunctionSpec) : m Term := do
  let params ← f.params.mapM fun p => do
    `(({ name := $(quote p.name), ty := $(← quoteParamType p.ty) } : Compiler.CompilationModel.Param))
  `(({ name := $(quote f.name), params := $(← list params), returnType := none,
       returns := $(← list (← f.returns.mapM quoteParamType)), isView := $(quote f.isView),
       body := $(← list (← f.body.mapM quoteStmt)) } : Compiler.CompilationModel.FunctionSpec))

def quoteModel (model : CompilationModel) : m Term := do
  `(({ name := $(quote model.name), constructor := none,
       fields := $(← list (← model.fields.mapM quoteField)),
       functions := $(← list (← model.functions.mapM quoteFunction)) } :
      Compiler.CompilationModel.CompilationModel))

private def strings (xs : List String) : m Term := list (xs.map quote)

def quoteReport (r : ImportReport) : m Term := do
  let fn (f : ImportedFunction) : m Term := do
    `(({ contract := $(quote f.contract), name := $(quote f.name), declId := $(quote f.declId),
         paramTypes := $(← strings f.paramTypes) } : Compiler.CompilationModel.SolidityImport.ImportedFunction))
  let proj (p : ParamProjection) : m Term := do
    `(({ function := $(quote p.function), parameter := $(quote p.parameter), member := $(quote p.member),
         structName := $(quote p.structName),
         headWord := $(quote p.headWord), modelParam := $(quote p.modelParam),
         ignoredMembers := $(← strings p.ignoredMembers) } :
        Compiler.CompilationModel.SolidityImport.ParamProjection))
  let opq (o : OpaqueMember) : m Term := do
    `(({ field := $(quote o.field), name := $(quote o.name), solcType := $(quote o.solcType),
         wordOffset := $(quote o.wordOffset), byteOffset := $(quote o.byteOffset) } :
        Compiler.CompilationModel.SolidityImport.OpaqueMember))
  let status (st : FunctionStatus) : m Term := do
    let proof ← match st.compilerProof with
      | .unavailable reason =>
        `(Compiler.CompilationModel.SolidityImport.CompilerProofStatus.unavailable $(quote reason))
    `(({ function := $(quote st.function), denoteCovered := $(quote st.denoteCovered),
         compilerProof := $proof } : Compiler.CompilationModel.SolidityImport.FunctionStatus))
  `(({ importerVersion := $(quote r.importerVersion), solcLongVersion := $(quote r.solcLongVersion),
       solcSha256 := $(quote r.solcSha256), settingsJson := $(quote r.settingsJson),
       sourceDigest := $(quote r.sourceDigest), contract := $(quote r.contract),
       roots := $(← strings r.roots),
       functions := $(← list (← r.functions.mapM status)),
       includedFunctions := $(← list (← r.includedFunctions.mapM fn)),
       excludedFunctions := $(← list (← r.excludedFunctions.mapM fn)),
       projections := $(← list (← r.projections.mapM proj)),
       storageFields := $(← strings r.storageFields),
       storageKeys := $(← list (← r.storageKeys.mapM fun (f, ks) => do `(($(quote f), $(← strings ks))))),
       opaqueMembers := $(← list (← r.opaqueMembers.mapM opq)),
       observesPanicPayload := $(quote r.observesPanicPayload) } :
      Compiler.CompilationModel.SolidityImport.ImportReport))

end Compiler.CompilationModel.SolidityImport
