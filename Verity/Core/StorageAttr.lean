import Lean

/-!
Simp-set attribute for the canonical ContractState storage lens API.
Lemmas tagged `@[storage_simps]` normalize lens reads over lens writes; the
P5 storage-representation flip swaps the lens implementations while keeping
this simp set as the stable proof surface.
-/

register_simp_attr storage_simps
