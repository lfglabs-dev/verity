import Compiler.SolidityImport.SolidityAbi

namespace Compiler.CompilationModel.SolidityImport.SolidityAbi

def canonicalMarket : List Nat := [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 9]

theorem prefix_load : loadWord 0x12345678 [2^255] 0 = 0x12345678 * 2^224 + 2^223 := by decide

theorem nonwrapping_load : loadWord 0x12345678 [2^255] (2^256-1) = 0 := by decide

theorem root_control : tupleHead? 0 canonicalMarket 2 0 8 = some 68 := by decide

theorem array_control : staticArrayView? 0 canonicalMarket 68 3 4 = some ⟨356, 1⟩ := by decide

theorem backwards_array_control :
    staticArrayView? 0 [64, 1, 31337, 2, 3, 2^256-32, 999, 500, 4, 5, 1, 6, 77, 88, 9]
      68 3 4 = some ⟨68, 1⟩ := by decide

theorem truncated_array_control :
    staticArrayView? 0 [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88]
      68 3 4 = none := by decide

theorem memory_array_control :
    memoryStaticArrayView 0 canonicalMarket 68 3 4 384 = .ok (⟨356, 1⟩, 448) := by rfl

theorem memory_backwards_rejected :
    memoryStaticArrayView 0 [64, 1, 31337, 2, 3, 2^256-32, 999, 500, 4, 5, 1, 6, 77, 88, 9]
      68 3 4 384 = .error .malformed := by rfl

theorem memory_allocation_before_truncation :
    memoryStaticArrayView 0 [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 2^59-1, 6, 77, 88, 9]
      68 3 4 384 = .error .allocation := by rfl

theorem memory_truncation :
    memoryStaticArrayView 0 [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88]
      68 3 4 384 = .error .malformed := by rfl

def collateralFields : List ScalarKind := [.address, .uint 31, .uint 31, .address]

theorem memory_element_control :
    readMemoryStaticElements 0 canonicalMarket collateralFields 356 448 1 =
      .ok ([[6, 77, 88, 9]], 576) := by rfl

theorem memory_unused_oracle_rejected :
    readMemoryStaticElements 0 [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 2^160]
      collateralFields 356 448 1 = .error .malformed := by rfl

theorem calldata_unused_oracle_not_read :
    readScalar 0 [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 2^160]
      356 .address = .ok 6 := by rfl

theorem scalar_bool_rejected : readScalar 0 [2] 4 .bool = .error .malformed := by rfl

theorem scalar_uint8_rejected : readScalar 0 [256] 4 (.uint 0) = .error .malformed := by rfl

end Compiler.CompilationModel.SolidityImport.SolidityAbi
