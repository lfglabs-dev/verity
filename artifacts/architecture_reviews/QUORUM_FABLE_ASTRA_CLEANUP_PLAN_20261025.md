# Quorum Architectural (Claude Fable 5.1 × GPT-6 Astra) — Audit des Specs, Plan d'Amélioration & Cleanup d'Abstractions (`Verity 2.0` × `EVMYulLean 2.0`)

- **Date** : 25 octobre 2026
- **Outillage unifié** : `Th0rgal/turbo-lean` @ `8f24bf8` (incluant `lean-native` v0.5.0 lié en C-ABI in-process, `lean-native-core` et `turbo-zygote`) + `Th0rgal/maxwell` (`Th0rgal/certified-research` @ `6cf83e5`).
- **Rapports détaillés des subagents du quorum** :
  - Voix **Claude Fable 5.1** (`anthropic/claude-fable-5-1`, mission `604b21b9-3fef-4675-bfb4-88cddf579713`) : [`quorum_fable_5_1_20261025.md`](quorum_fable_5_1_20261025.md)
  - Voix **GPT-6 Astra** (`openai/gpt-6-astra`, mission `b076c416-9799-48e6-baa6-0b36341d6df0`) : [`quorum_gpt_6_astra_20261025.md`](quorum_gpt_6_astra_20261025.md)

---

## 1. Consensus du Quorum sur l'Audit des Spécifications (`Verity 2.0` & `EVMYulLean 2.0`)

Bien que `turbo-lean --json audit-spec` valide **100 % des spécifications** comme `non_vacuous_and_tight` (`0 vacuous_specs`, `0 trivial_specs` après correction des deux lemmes `0 ≤ n` dans `YulEvmGasEquivalence.lean`), Fable 5.1 et GPT-6 Astra convergent sur une distinction fondamentale :
> **Un théorème peut être syntaxiquement `non_vacuous_and_tight` tout en portant sur un modèle fantôme détaché (*Shadow Model*) ou une projection tautologique (`P ∧ Q → P`).**

### Matrice de Connectivité Sémantique des Specs

| Module | Dépôt | Théorèmes (`audit-spec`) | Verdict du Quorum (Fable 5.1 × GPT-6 Astra) |
|---|---|---:|---|
| `EvmYul/UInt256.lean` & `Specs/UInt256BitVecBridge.lean` | `EVMYulLean 2.0` | `20 + 17` | **Connecté (Fondation L0)** : `UInt256` adossé à `BitVec 256` avec projection `val : Fin (2^256)` zéro-coût et preuves `bv_decide`. |
| `EvmYul/EVM/Gas.lean` & `Specs/GasSpec.lean` & `Specs/ConformMultiFork.lean` | `EVMYulLean 2.0` | `12 + 10` | **Connecté (Fondation L0/L3)** : Fonctions de coût pures totales sans `!` (`CsloadPure`, `CsstorePure`, `Ckeccak256Pure`, `ClogPure`, `Cₘ`, `L`, `intrinsicGas`) paramétrées par `Fork` (`Shanghai..Osaka`). |
| `EvmYul/MetaSpecs/DialectCommutation.lean` | `EVMYulLean 2.0` | `12` | **Connecté à `EvmYul.step`** : Prouve la commutation `step (.Yul)` ↔ `step (.EVM)` sur 14 instructions partagées. *À étendre* : ajouter `MLOAD`, `MSTORE`, `MSTORE8`, `SSTORE`, `TSTORE`. |
| `EvmYul/MetaSpecs/StateLensAlgebra.lean` | `EVMYulLean 2.0` | `65` | **Connecté à `State.sstore`** (`sstore_eq_storageLens`) + algèbre générique `StateLens`. Instance `LawfulBEq UInt256` dupliquée nettoyée. |
| `EvmYul/Yul/GasInterpreter.lean`, `MessageCallCombinator.lean`, `MetaSpecs/StaticCallAndRollback.lean`, `MetaSpecs/GasTermination.lean` | `EVMYulLean 2.0` | `5 + 4 + 8 + 11` | **Modèles purs non encore câblés dans `Yul/Interpreter.lean:primCall`** : Leur non-branchement masque **4 bugs dans `Yul/Interpreter.lean`** (rejet erroné de `STATICCALL` imbriqué ligne 172, écrasement de `calldata := default` au retour d'appel externe, oubli de restauration de `sender`/`depth`, et absence d'appel à `consumeYulGas`). |
| `Verity/Specs/Common.lean` & `Composition.lean` | `Verity 2.0` | `42` | **Connecté à `Denote.ContractState`** (`FnSpec.Satisfies`, `unchangedExcept`, `WritesOnly`), mais coexiste avec ~400 LOC de prédicats historiques `same*Context`. |
| `Verity/Specs/ObsAlgebra.lean` | `Verity 2.0` | `13` | **Partiellement détaché** : `Obs` et `solidityArrayElemSlot` sont propres et injectifs, mais il manque la typeclass `HasObs` projetant `Denote.ContractState`, `IRState`, `EvmYul.Yul.State` et `EvmYul.EVM.State` vers `Obs`. |
| `Verity/Specs/AdversaryAndHelpers.lean` & `GuardAndDynamicAbi.lean` | `Verity 2.0` | `11 + 8` | **Modèles fantômes / Tautologies de projection** : `ValidAdversaryStep` projette ses propres champs au lieu d'importer `EvmYul.MetaSpec.StaticCallAndRollback` ; `runNonReentrantGuarded` opère sur un état jouet au lieu de `attachNonReentrantGuard`. |
| `Compiler/Proofs/YulGeneration/BytecodeTranslationValidation.lean` | `Verity 2.0` | `5` | **Demi-connecté** : Le scanner `scanValidJumpdests` est réellement branché sur `EvmYul.EVM.nextPcAfterOp`, mais `checkBytecodeBlockCert` compare deux `Nat` pré-calculés (`evmSlicePostDigest = yulBlockPostDigest`) au lieu d'exécuter symboliquement les blocs. |
| `Compiler/Autoresearch/MaxwellGasSuperoptimizer.lean` & `AccelPlugin.lean` | `Verity 2.0` | `87 + 10` | **Dette d'abstraction critique (1 412 LOC)** : L'enum plat `G1..G55` et `verifiedAccelTheoremAllowlist : List String` mélangent 8 vraies passes d'optimisation (`G1`–`G8`) avec 47 lemmes arithmétiques génériques sur `Nat` et 32 contre-exemples constants (`42 ≠ 99`), non câblés dans `Codegen.emitYul`. |

---

## 2. Plan d'Amélioration Priorisé (Sûreté TCB × Performance Gaz × Performance Preuve)

### Priorité 1 — Sûreté & Réduction de la TCB (Fermer l'écart Modèle ↔ Exécution)
1. **Corriger les 4 bugs de `EvmYul/Yul/Interpreter.lean` en y branchant `MessageCallCombinator` + `GasInterpreter` + `StaticCallAndRollback`** :
   - Remplacer les ~320 lignes dupliquées de `primCall` (`.CALL`, `.STATICCALL`, `.CALLCODE`, `.DELEGATECALL`) par un appel unique à `prepareChildCallEnv` + restauration complète de `executionEnv` (`calldata`, `sender`, `depth`, `perm`) + capture de `.error .Revert` via `resolveFrameTermination` + déduction `consumeYulGas`.
2. **Connecter `HasObs` aux 4 couches et dériver `AdversaryAndHelpers` depuis `EvmYul/MetaSpecs/`** :
   - Instancier `HasObs` sur Layer 1 (`Denote`), Layer 2 (`IR`), Layer 3 (`EvmYul.Yul`) et EVM (`EvmYul.EVM`).
   - Dériver les lois d'immutabilité `STATICCALL` et de rollback sur `REVERT` dans Verity directement depuis `EvmYul.MetaSpec.StaticCallAndRollback` et `DialectCommutation` (étendu à `MLOAD`/`MSTORE`/`SSTORE`/`TSTORE`).
3. **Remplacer la confiance nominale (`List String` et digests libres) par des témoins calculés** :
   - Dans `AccelPlugin.lean` : remplacer `verifiedAccelTheoremAllowlist : List String` par une structure `VerifiedPass` portant sa preuve `ObsRefines` et `gasLe`.
   - Dans `BytecodeTranslationValidation.lean` et `SolcoreBridge` : calculer les résumés symboliques directement par évaluation sur l'AST/bytecode au lieu de comparer deux entiers fournis dans le certificat.

### Priorité 2 — Performance Gaz (Câbler les 8 Passes Réelles dans `Codegen.lean`)
Au lieu de 55 étiquettes déclaratives, câbler effectivement dans `emitYulWithProfile` les **8 passes de transformation d'AST** à fort gain mesuré par `EvmYul.Specs.yulStepTotalGas` :
1. **Niveau IR (`IRContract → IRContract`)** :
   - **P-IR1 (`SlotCoalescing`)** : fusion des lectures/écritures de sous-mots packés sur un même slot (`-200` à `-600` gaz/appel).
   - **P-IR2 (`CalldataLazyDecoding`)** : lecture `calldataload` paresseuse sans copie mémoire morte.
   - **P-IR3 (`StoreLoadForwarding`)** : transfert `SSTORE → SLOAD` et `TSTORE → TLOAD` intra-bloc + élision des écritures idempotentes (`NoInterveningClobber`).
   - **P-IR4 (`CheckedArithIntervalAndWadRay`)** : élision des gardes d'overflow sous borne d'intervalle (`require(x <= y)`) et spécialisation `mulDivDown/Up` → `wMulDown/Up`.
2. **Niveau Yul (`YulObject → YulObject`)** :
   - **P-Yul1 (`TempReuse` + `computedSpillBase`)** : déjà branché, évite l'expansion mémoire à `0x1000`.
   - **P-Yul2 (`MappingSlotCSE`)** : factorisation de `keccak256(k, slot)` sur les accès `read-modify-write`.
   - **P-Yul3 (`ScratchSpaceHashing`)** : hachage `0x00..0x3f` sans bump du pointeur libre `0x40`.
   - **P-Yul4 (`SelectorDispatchTree`)** : arbre binaire de recherche $O(\log N)$ dans `buildSwitch` dès $N \ge 6$.

### Priorité 3 — Performance Compilation & Preuve (`turbo-lean` + `lean-native` + `BitVec 256`)
1. **Unifier `Verity.Core.Uint256` comme `abbrev Uint256 := EvmYul.UInt256`** :
   - Élimine 600+ lignes de preuves `Nat.mod` manuelles au profit de `BitVec 256` + `bv_decide` ($< 5\text{ ms}$) et du fast-check C-ABI `Word256` de `turbo-lean` (`8f24bf8`).
2. **Scinder `SupportedSpec.lean` (7 068 LOC)** en 5 sous-modules parallèles (`Params`, `Events`, `Errors`, `Statements`, `Bridge`) pour diviser par 4 le temps de recompilation incrémental sous `turbo-lean`.
3. **Éliminer l'inductif plat à 55 constructeurs `GasOptimizationPassId`** qui dégrade l'élaboration de Lean 4.

---

## 3. Plan de Cleanup Chirurgical du Code et des Specs (Les 4 Couches d'Abstraction Cibles)

| Couche | Abstraction Unique Cible | Fichiers Unifiés / Nettoyés | Gain de Code & Clarté |
|---|---|---|---|
| **Layer 0 : Mots 256 bits, Lentilles d'État & Gaz Pur** | • `Verity.Core.Uint256 := EvmYul.UInt256` (`BitVec 256`)<br/>• `EvmYul.MetaSpec.StateLens` instancié sur `LogicalStorageLoc` (L1/L2) et `PhysicalStorageKey` (L3/EVM)<br/>• `EvmYul.EVM.Gas` comme unique source des constantes et formules de gaz | • Fusionne `Verity/Core/Uint256.lean` + `UInt256BitVecBridge.lean`<br/>• Fusionne `StorageLoc` (`SourceSemantics.lean`), `SpecStorageKey` (`Common.lean`) et `ExtendedStorageKey` (`ObsAlgebra.lean`)<br/>• Fusionne `GasCostModel.lean` + `EvmYulGasAdapter.lean` | **-1 100 LOC** de définitions et lemmes dupliqués |
| **Layer 1 : Spécifications Totales (`FnSpec`), `Frame` & `HasObs`** | • Prédicat unique `Frame (W : Finset LogicalStorageLoc) (s s' : ContractState)`<br/>• Typeclass `HasObs σ` + `ObsRefines` sur les 4 couches | • Déprécie et supprime les ~400 LOC de `sameStorage*Context` dans `Verity/Specs/Common.lean`<br/>• Connecte `ObsAlgebra.lean` à `Denote`, `IR`, `Yul` et `EVM` | **-400 LOC** de prédicats combinatoires ad-hoc |
| **Layer 2 : Résumés d'Effets IR, Gardes & Réécritures par Famille** | • `helperGraph (c : CompilationModel)` extrait de l'AST réel<br/>• `Rewrite` typé indexé par `Family` (`arith \| bitmask \| stack \| storage \| control \| zeroElision`) | • Remplace `MaxwellGasSuperoptimizer.lean` (1 412 LOC, `G1..G55` + 32 `*_refuted` triviaux) par `BitVec256Lemmas.lean` + `Compiler/Rewrites/` | **-950 LOC** de bruit algébrique et de tables statiques |
| **Layer 3 : Pipeline Porteur de Preuves (`VerifiedPass`) & Pont `EvmYul`** | • `Pipeline.run (passes : List VerifiedPass)` directement appelé par `Codegen.emitYul`<br/>• `Yul/Interpreter.lean:primCall` câblé sur `MessageCallCombinator` + `GasInterpreter` | • Remplace `verifiedAccelTheoremAllowlist : List String` dans `AccelPlugin.lean`<br/>• Dé-duplique 320 LOC dans `EvmYul/Yul/Interpreter.lean` et corrige les 4 bugs d'appel Yul | **-450 LOC** + fermeture complète de la TCB d'optimisation |
