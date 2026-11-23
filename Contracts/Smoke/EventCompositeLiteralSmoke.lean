import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
`emit` with fixed-shape literal arguments: an array of structs whose last member is itself an
array, and `bytes`, built in the body (EIP-2535's `DiamondCut` shape). Each literal's layout is
fixed at compile time, so the event data is constant offset and length words plus the leaves.
`test/EventCompositeLiteralSmoke.t.sol` compares every log with solc's byte for byte.
-/
verity_contract EventCompositeLiteralSmoke where
  storage

  struct Cut where
    target : Address,
    action : Uint8,
    selectors : Array Bytes4

  event_defs
    event Cuts(cuts : Array Cut, init : Address, data : Bytes)
    event Pair(left : Uint256, values : Array Uint256, right : Uint256)

  constants
    NO_INIT : Uint256 := 0

  -- one cut of one selector, emitted from an internal function
  function internal emitOne (target : Uint256, action : Uint256, sel : Uint256) : Unit := do
    emit "Cuts" [[⟨target, action, [sel]⟩], NO_INIT, emptyBytes]

  function cutOne (target : Uint256, action : Uint256, sel : Uint256) : Unit := do
    emitOne target action sel

  -- two cuts, one and three selectors, and a non-zero `init`
  function cutTwo (a : Uint256, b : Uint256, s0 : Uint256, s1 : Uint256, s2 : Uint256,
      s3 : Uint256, init : Address) : Unit := do
    emit "Cuts" [[⟨a, 0, [s0]⟩, ⟨b, 2, [s1, s2, s3]⟩], init, emptyBytes]

  -- a dynamic word array literal between two scalars
  function pair (x : Uint256, y : Uint256, z : Uint256) : Unit := do
    emit "Pair" [x, [y, z, add y z], z]

/-- The executable `emit` records the literal's ABI encoding: `cutOne` logs one `Cuts` event whose
words are the cut array's tail (count, element offset, target, action, selectors offset, selector
count, selector), then `init` (0) and the empty `bytes` (length 0). Leaves are cleaned as solc
does: `target` to 160 bits, `action` to 8 bits, `sel` to its high 4 bytes. -/
theorem cutOne_logs_abi_encoding (target action sel : Uint256) (s : ContractState) :
    ∃ s', (EventCompositeLiteralSmoke.cutOne target action sel).run s = .success () s' ∧
      s'.events = s.events ++ [{
        name := "Cuts"
        args := [1, 32, target.val % 2 ^ 160, action.val % 2 ^ 8, 96, 1,
            sel.val / 2 ^ 224 % 2 ^ 32 * 2 ^ 224, 0, 0].map Verity.Core.Uint256.ofNat
        indexedArgs := [] }] := by
  refine ⟨_, rfl, ?_⟩
  simp [Compiler.CompilationModel.abiLitWords, Compiler.CompilationModel.abiLitEncode,
    Compiler.CompilationModel.abiLitEncodeItems, Compiler.CompilationModel.abiLitLayoutSeq,
    Compiler.CompilationModel.abiLitBaseType, Compiler.CompilationModel.abiLitLeafType?,
    Compiler.CompilationModel.abiLitNormalizeWord, Compiler.CompilationModel.isDynamicParamType,
    Compiler.CompilationModel.isDynamicParamTypeList,
    EventCompositeLiteralSmoke.__eventParamTypes_Cuts, EventCompositeLiteralSmoke.NO_INIT,
    pure, Except.pure, bind, Except.bind]

end Contracts.Smoke
