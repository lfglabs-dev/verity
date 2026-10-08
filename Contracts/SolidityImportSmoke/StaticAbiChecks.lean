import Verity.Core.Model.DynamicAbi

namespace SolidityImportSmoke.StaticAbiChecks
open Compiler.CompilationModel Compiler.CompilationModel.DynamicAbi

-- These exercise the public decoder, including progression past a tuple.
theorem flat_tuple_followed_by_scalar : bindExternalParams 0
    [{ name := "s", ty := .tuple [.uint256, .uint256] }, { name := "x", ty := .uintN 8 }]
    [11, 22, 255] = some [("s_0", 11), ("s_1", 22), ("x", 255)] := by decide +kernel

theorem nested_tuple_offsets : bindExternalParams 0
    [{ name := "s", ty := .tuple [.uint256, .tuple [.uint256, .bool]] },
     { name := "x", ty := .address }]
    [11, 22, 1, 17] = some [("s_0", 11), ("s_1_0", 22), ("s_1_1", 1), ("x", 17)] := by decide +kernel

theorem truncated_tuple_rejected : bindExternalParams 0
    [{ name := "s", ty := .tuple [.uint256, .uint256] }]
    [11] = none := by decide +kernel

theorem dynamic_leaf_rejected : bindStaticTupleType 0 [32, 0] "s" (.tuple [.bytes]) 4 = none := by decide +kernel

theorem fixed_array_leaf_rejected : bindExternalParams 0
    [{ name := "s", ty := .tuple [.fixedArray .uint256 2] }]
    [11, 22] = none := by decide +kernel

end SolidityImportSmoke.StaticAbiChecks
