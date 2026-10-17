import Compiler.Proofs.IRGeneration.NativeConstructorMemory
import Compiler.Proofs.IRGeneration.NativeConstructorCopyStep
import Compiler.Proofs.IRGeneration.NativeConstructorOutputRule
import Compiler.Proofs.IRGeneration.NativeConstructorStackSteps
import Compiler.Proofs.IRGeneration.NativeConstructorGas

/-! Native constructor memory, stack and local gas laws. Concrete whole-X
output/gas correspondence and Lambda account commits remain separate obligations. -/
