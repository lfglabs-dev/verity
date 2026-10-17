import Compiler.ECM

/-! Data-only Solidity staticcall module, shared with the compiler-free ECM
leaf. Canonical compilation ignores opaque closures for tagged transports. -/
namespace Compiler.Modules.SolidityStaticCall

abbrev compileUint256 := Compiler.ECM.SolidityStaticCall.compileUint256
abbrev uint256Module := Compiler.ECM.SolidityStaticCall.uint256Module

end Compiler.Modules.SolidityStaticCall
