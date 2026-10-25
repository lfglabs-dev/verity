# Synthèse Architecturale & Plan d'Exécution Unifié — Verity 2.0 × `EVMYulLean 2.0`
## Consensus des 3 Modèles (`anthropic/claude-fable-5-1`, `openai/gpt-6-astra`, `builtin/smart`)

- **Revue Claude Fable 5.1** : [`review_fable_5_1.md`](review_fable_5_1.md)
- **Revue GPT-6 Astra** : [`review_gpt_6_astra.md`](review_gpt_6_astra.md)
- **Revue OpenCode `builtin/smart`** : [`review_opencode_builtin_smart.md`](review_opencode_builtin_smart.md)

---

## 1. Principe Directeur Unanime : « Le Pipeline Prouvé et le Pipeline Exécuté Doivent Être la Même Fonction »

Les trois modèles convergent sur un diagnostic central :
> **Toute preuve portant sur un shim, un pack de réécriture ou un arbre de dispatch que `Compiler/Codegen.lean` n'appelle pas sur le chemin actif a une valeur nulle du point de vue de la TCB.**

Aujourd'hui, Verity possède déjà une pile formelle remarquable (`FnSpec.Satisfies`, `unchangedExcept`, `compile_preserves_semantics`, 36/36 builtins pontés vers `EVMYulLean 2.0`, 255 théorèmes `EVMYulLean 2.0` sans `sorryAx` ni `native_decide`), mais **trois fractures** séparent encore cette fondation d'un compilateur intégralement vérifié et compétitif en gaz :
1. **L'algèbre d'observation (`Obs`) et l'algèbre des clés de stockage (`SpecStorageKey`)** doivent être élargies *avant* de brancher les passes d'optimisation (pour inclure `logs`, `returndata`, `transientStorage`, et corriger la dérivation des slots de tableaux dynamiques `keccak256(pad32(s)) + i * stride`).
2. **Les briques prouvées en isolation** (`CertifiedPatchPack`, `SlotCoalescingShim`, `SelectorDispatchTree`, `TempReuse`, `VerifiedECMShims`, `SupportedHelperSummaryProofCatalog`) doivent devenir les **étapes mêmes de `Codegen.lean`** via une configuration porteuse de preuves (`PipelineConfig fork` / `CodegenProfile`).
3. **Les deux frontières externes de la TCB** (`Import.lean` en entrée et `solc --strict-assembly` en sortie) doivent être transformées en **producteurs non fiables validés par témoins** (`CertifiedContractTranslationWitness` côté `SolcoreBridge`, et `BytecodeTranslationValidation` / `Assemble.sim` côté `EVMYulLean 2.0`).

---

## PARTIE 1 — Comment Terminer Proprement Toutes les Phases Restantes de la Roadmap Verity

### Phase A — Unification de l'Algèbre d'Observation (`Obs`) et des Clés de Stockage (`SpecStorageKey`) [Prérequis P0]

1. **Observation canonique `Obs` (`Verity/Specs/Common.lean` & `Compiler/Proofs/EndToEnd.lean`)** :
   - Unifier l'observation entre Layer 1 (`Denote`), Layer 2 (`IRInterpreter`), Layer 3 (`EvmYul.Yul`) et `EvmYul.EVM` :
     ```lean
     structure Obs where
       status     : ExecStatus          -- success | revert | invalid
       returndata : ByteArray           -- ABI return ou sélecteur + payload d'erreur
       logs       : List Log            -- emitter × topics[≤4] × data
       storage    : List (SpecStorageKey × UInt256)
       transient  : List (SpecStorageKey × UInt256)
     ```
   - **Séparation stricte** entre l'équivalence fonctionnelle (`ObsEquiv a b : Prop := a = b`, sous hypothèse de gaz suffisant) et le raffinement de gaz (`improves_cost : GasInterpreter.used fork (apply x) σ ≤ GasInterpreter.used fork x σ`). Comme le soulignent GPT-6 Astra et `builtin/smart`, le gaz ne doit pas être dans `ObsEquiv` sous peine d'interdire toute optimisation réduisant le coût en gaz.
2. **Correction de la dérivation des tableaux dynamiques (`SourceSemantics.lean` vs Yul)** :
   - Actuellement, `SourceSemantics` utilise `solidityMappingSlot s i` (`keccak256(abi.encode(i, s))`) pour les éléments de tableaux dynamiques alors que Yul émet la formule Solidity standard `keccak256(bytes32(s)) + i * stride`.
   - Étendre `SpecStorageKey` avec `.arrayElem (slot : UInt256) (i stride : Nat)` et `.bytesData (slot : UInt256) (byteOff : Nat)` où `arrayBase s := keccak256 (pad32 s)` et `keyAddr (.arrayElem s i stride) := (arrayBase s + i * stride) mod 2^256` (avec garde de non-wrap).
   - Dériver l'injectivité (`keyAddr_inj`) et la disjonction mapping vs array (`arrayElem_not_mapWord`) comme corollaires d'un **unique axiome Keccak borné** (`keccak256_inj_on_lt_2_256` sur préimages $\le 128$ octets).

---

### Phase B — Clôture de Layer 2 : Whole-Contract Completeness (`#1630` / `#1638`)

1. **Élimination de `helperSurfaceClosed` via `SupportedHelperSummaryProofCatalog`** :
   - Étendre le catamorphisme unique `StmtFeatureMask` (`UsageAnalysis.lean`) avec `helperIds : Finset InternalId`.
   - Décharger le théorème d'induction `CompiledStmtStepWithHelpersAndHelperIR` (`GenericInduction.lean`) en consommant `SupportedHelperSummaryProofCatalog` :
     - Pour les graphes d'appels internes acycliques (SCC de Tarjan triviales) : induction topologique où chaque `HelperSummary` est prouvé une seule fois (`agree : IR.denote s.id = HelperSummary.denote s`) et appliqué à chaque site d'appel (`Stmt.internalCall`, `Stmt.internalCallAssign`, `Expr.internalCall`) via la règle de frame `unchangedExcept`.
     - Pour les appels récursifs : induction bien fondée sur la mesure lexicographique `(1024 - depth, gasAvailable)` fournie par `EVMYulLean 2.0` (`MetaSpec.GasTermination`).
   - Dériver l'ancien prédicat comme simple cas particulier (`helperSurfaceClosed_of_catalog`) pour préserver toutes les preuves existantes sans rupture.
2. **Unification `AdversaryModel` en 6 PRs atomiques (C1 → C6)** :
   - **C1** : Définir `AdversaryModel` (`none | staticView | callback | lowLevel | any`) et ses 5 lois (`frame`, `static_no_write`, `rollback`, `ret_bound`, `reenter_fuel`) dans `Verity/Specs/Adversary.lean`.
   - **C2** : Émettre `AdversaryModel` depuis `Verity/Macro/*` dans `FnSpec` et supprimer le second enum redondant.
   - **C3** : Unifier `external`, `call`, `delegatecall`, `staticcall` dans `SourceSemantics` autour d'un unique `execCall model`.
   - **C4** : Réduire `Reentrancy.lean` et `CallbackBridge.lean` à des corollaires des lois `frame` + `rollback` sous `.callback`.
   - **C5** : Prouver que l'abaissement IR préserve le modèle (`STATICCALL` ssi `staticView`, `DELEGATECALL` sous `lowLevel`).
   - **C6** : Stocker `AdversaryModel` dans `SupportedSpec.effects` et quantifier le théorème contrat entier dessus.
3. **`nonreentrant` (EIP-1153) *à l'intérieur* de `SupportedSpec`** :
   - Déplacer l'élaboration du verrou `TLOAD`/`TSTORE` (`attachNonReentrantGuard`) **avant** `compileFunctionSpec` (dans `CompilationModel`), pour que `FnSpec.Satisfies` voie réellement le garde.
   - Utiliser `MetaSpec.StaticCallAndRollback` d'`EVMYulLean 2.0` pour prouver que sur `revert`, le slot transitoire est restauré, et que sous `AdversaryModel.callback`, toute réentrance trouve `tload(lock) = ENTERED` et emprunte la branche `.revert`.
4. **Événements dynamiques et erreurs personnalisées composites (`#2082`)** :
   - Partager un unique encodeur ABI vérifié (head à `[0:32*n)`, tails concaténés à `__evt_data_tail`, offsets relatifs au début du bloc d'arguments) entre `Log.data` et `RevertObs.data`, et brancher `VerifiedECMShims.dynamicAndStructEvent` directement dans `Codegen.lean`.

---

### Phase C — Branchement du Pipeline Layer 3 & Unification du Modèle de Gaz

1. **Refactorisation non-cassante de `Compiler/Codegen.lean` par `PipelineConfig fork`** :
   - Paramétrer `Codegen.emitYul` par `cfg : PipelineConfig fork` regroupant `exprPack`, `stmtPack`, `blockPack`, `objectPack`, `dispatch : .linear | .tree`, `coalesce : Bool`, et `tempReuse`.
   - Prouver `legacy_eq_old_codegen : lowerIR .legacy c = Codegen.old c := rfl` pour garantir 100 % de compatibilité avec les parity packs existants, puis activer `PipelineConfig.optimized fork`.
2. **Ordre fixe de composition des passes certifiées** :
   ```text
   lowerIR → objectPack → dispatch (.linear | .tree) → blockPack
           → slotCoalesce (si cfg.coalesce) → stmtPack → exprPack → tempReuse
   ```
   - **`SelectorDispatchTree`** : Prouver `dispatchTree_eq_linear` par induction sur la liste triée sans doublons `fs : List (Selector × Yul.Block)` après masquage `and(sel, 0xffffffff)`.
   - **`SlotCoalescingShim`** : Intégrer la CSE `SLOAD` intra-bloc et la fusion d'écritures packées (`BitVec 256` masks disjoints) sous une condition d'absence de clobber décidable (`NoInterveningClobber` : aucun `SSTORE` vers `keyAddr` aliassé, aucun `CALL`/`DELEGATECALL` dont `victimWrites` contient la clé). Pour le hissage inter-branches (`if`), l'effectuer au niveau `TypedIR` (Layer 2) où les frames `StorageLoc` sont explicites.
3. **Unification de `Verity.Autoresearch.GasCostModel` avec `EVMYulLean 2.0`** :
   - Remplacer les constantes statiques approximatives de `GasCostModel.lean` par un adaptateur direct vers `EvmYul/EVM/Gas.lean` et `EvmYul/Yul/GasInterpreter.lean` (`evalYulStmtCharged`), paramétré par `Fork` (`Shanghai`, `Cancun`, `Prague`, `Osaka`) et un contexte d'accès warm/cold (`AccessWarmth`) + taille mémoire (`memWords`) pour refléter exactement l'expansion mémoire quadratique et EIP-2929/2200/3529.

---

### Phase D — Clôture de `BridgedSafeStmts` & Sortie de `solc` et `Import.lean` de la TCB

1. **Clôture programme-entier de `BridgedSafeStmts` (`EvmYulLeanBodyClosure.lean` & `EndToEnd.lean`)** :
   - Figer la table complète des helpers (`IRContract.internalFunctions` + stubs externes + `VerifiedECMShims` au statut `.proved`) et prouver un théorème de clôture indexé par cet environnement, éliminant les hypothèses ouvertes sur `internalCall`, `internalCallAssign`, `externalCallBind` et `Stmt.ecm`.
2. **Sortie de `solc --strict-assembly` de la TCB (Deux étages complémentaires)** :
   - **Court terme (Translation Validation du bytecode produit par `solc`)** : Construire `Compiler/Proofs/YulGeneration/BytecodeTranslationValidation.lean` qui désassemble le bytecode émis par `solc --strict-assembly` en CFG de blocs de base via `JumpdestTotal.D_J_total` (`EVMYulLean 2.0`), vérifie par simulation symbolique (`MetaSpec.DialectCommutation`) que chaque bloc EVM raffine le bloc Yul correspondant, et rejette en mode fail-closed toute divergence.
   - **Moyen terme (Assembleur Yul → EVM vérifié `EvmYul/Assemble.lean`)** : Pour le Yul structuré émis par Verity (profondeur d'expressions bornée par `TempReuse`, appels internes résolus par table), écrire un abaissement direct `assemble : YulObject → ByteArray` avec sa preuve `Assemble.sim` sur `EvmYul.EVM.Semantics`, supprimant totalement l'appel à `solc` pour la compilation native Verity.
3. **Sortie de `Compiler/SolidityImport/Import.lean` (15,7k LOC) de la TCB** :
   - Faire de `solidity_import` un producteur non fiable qui génère à la fois le `CompilationModel` et une tactique automatique `prove_translation_witness` produisant un `CertifiedContractTranslationWitness` (`TranslationValidation.lean` / `SolcoreBridge.lean`) par normalisation symbolique entre l'AST Solcore/Yul importé et `Denote.execStmtList`.

---

## PARTIE 2 — Plan d'Optimisation de Gaz Formellement Prouvé sur le Corpus Réel Ethereum & Détection de Bugs `solc`

### 2.1 Ingestion Massive de Tous les Contrats Ethereum via `solidity_import`

1. **Construction du Corpus Reproductible (`benchmarks/corpus/`)** :
   - **Sourcify** (snapshot complet par hash normalisé d'entrée compilateur) + **Top-TVL Etherscan** (Uniswap v2/v3/v4, Aave v3, Morpho Blue, Maker/Sky, Curve, Balancer, Lido, Pendle, EigenLayer, Seaport, ERC-4337 EntryPoint) + **Suites de référence épinglées** (OpenZeppelin v4/v5, Solady, Solmate).
   - Chaque entrée conserve un manifeste déterministe : `chainId`, `address`, `solcVersion`, `optimizerRuns`, `viaIR`, `evmVersion`, `libraries`, `constructorArgs`, et statut sur l'échelle à 5 niveaux : **`Parsed → Imported → Compiled → Executed (4-way) → Proved`**.
2. **Élargissement ciblé de `Import.lean`, `EmitVerity.lean` et `InlineAssemblyShims.lean`** :
   - Prioriser par fréquence mesurée dans `Coverage.lean` :
     1. Linéarisation d'héritage C3, résolution des surcharges, inlining structuré des `modifier`s, et bibliothèques `using L for T`.
     2. Types entiers sous-256 bits (`uint8..uint128`, `int8..int256`), nettoyages explicites (`mask`/`signextend`), blocs `unchecked`, et ordre d'évaluation strict.
     3. Structures et tableaux imbriqués en stockage (`mapping(K => Struct[])`, `bytes`/`string` court vs long sur 31 octets).
     4. `try / catch` abaissé vers `externalCallBind` + décodage conditionnel de `returndata`.
     5. **Reconnaissance sémantique d'assembleur inline (`InlineAssemblyShims.lean` → `VerifiedECMShims.lean`)** : remplacer la correspondance syntaxique fragile par une normalisation de sous-graphes Yul vers un catalogue de ~25 idiomes certifiés (transferts ERC20 Solady/SafeERC20, `mulDiv` 512 bits `mulmod`/`sub`/`mul`, hachage scratch-space `0x00..0x3f`, lectures/écritures packées, verrous EIP-1153 `tload`/`tstore`, `mcopy`, proxies ERC-1167/EIP-1967).

---

### 2.2 Rejeu Automatisé des Suites de Tests & Harnais Différentiel 4-Voies

1. **Substitution Transparente d'Artefacts dans Foundry / Hardhat (`verity-forge-dropin`)** :
   - Script qui intercepte `out/<Contract>.sol/<Contract>.json` après `forge build`, compile le contrat via `solidity_import → EmitVerity → verity-compiler`, remplace `bytecode.object` et `deployedBytecode.object` en préservant l'ABI et le `storageLayout`, puis relance `forge test --gas-report` sans modifier une seule ligne des tests originaux du protocole.
2. **Harnais d'Équivalence Différentielle à 4 Voies** :
   - Pour chaque appel issu des suites Foundry/Hardhat, d'EEST (`ethereum/execution-spec-tests`) et de traces historiques mainnet :
     - **Voie A (`solc` Référence)** : Bytecode `solc` (Legacy et `--via-ir --optimize`) exécuté sur `revm` / `evmone`.
     - **Voie B (Verity Layer 1)** : `Denote.execStmtList` sur le `CompilationModel` importé.
     - **Voie C (Verity Layer 3 Yul)** : `EvmYul.Yul.GasInterpreter.evalYulStmtCharged` (`EVMYulLean 2.0`).
     - **Voie D (Verity Bytecode EVM)** : Bytecode compilé par Verity exécuté sur `revm` et `evmyul-t8n` (`EVMYulLean 2.0` EVM).
   - Vérification automatique de `ObsEquiv` (`status`, `returndata`, `logs`, `storage`, `transient`) entre A, B, C, D et profilage du delta de gaz $\Delta\text{Gas} = \text{Gas}(D) - \text{Gas}(A)$ par fonction et par bloc de base.

---

### 2.3 Taxonomie des Inefficacités de Gaz & Boucle Autonome `maxwell` + `ShimArena` + `CertifiedPatchPack`

Les trois revues identifient **7 sources majeures de surcoût en gaz** à éliminer par passes certifiées :

| # | Source de perte de gaz dans Verity | Passe d'optimisation certifiée à synthétiser & prouver | Niveau | Gain typique |
|---|---|---|---|---|
| **G1** | **Spills mémoire `TempReuse` au-dessus de `0x1000`** déclenchant un coût d'expansion mémoire quadratique (`C_mem(0x1000) ≈ 392+ gas`) | Remplacer la base fixe `0x1000` par le filigrane statique du contrat (`maxStaticMemOffset`, typiquement `0x80` ou `0x100`) et ordonnancer les expressions (Sethi-Ullman) pour rester dans les 16 slots de pile EVM | Layer 3 (`TempReuse.lean`) | **350 – 800 gas / appel** |
| **G2** | **`SLOAD` redondants intra/inter-branches & écritures packées séparées** (`SSTORE` multiples sur un même slot packé) | Activer `SlotCoalescingShim` en intra-bloc + hissage `IRPass.hoistInvariantSload` en Layer 2 (`TypedIR`) appuyé sur `StateLensAlgebra` | Layer 2 + Layer 3 (`SlotCoalescingShim.lean`) | **100 – 5 000+ gas / appel** |
| **G3** | **Recalcul répété de `keccak256(key . slot)`** lors d'un `read-modify-write` sur `mapping[k]` (ex. `balances[from] -= x`) | CSE de l'adresse de slot dérivée (`let slot_addr := mappingSlot(s, k)`) partagée entre le `sload` et le `sstore` | Layer 2 (`IRGeneration`) + `BlockPatchRule` | **42 – 90 gas / accès mapping** |
| **G4** | **Vérifications d'overflow/underflow redondantes** alors que les préconditions (`require(x <= balance)`) ou les masques de types garantissent déjà la borne | Analyse d'intervalles certifiée (`VerifiedIntervalAnalysis.lean` sur `BitVec 256`) réécrivant `checkedSub`/`checkedAdd` en `sub`/`add` Yul | Layer 2 (`TypedIR`) + `ExprPatchRule` | **25 – 60 gas / op arithmétique** |
| **G5** | **Allocation mémoire bump (`0x40`)** pour des hachages ou appels éphémères tenant dans le scratch space | Utiliser `0x00..0x3f` pour les hachages $\le 64$ octets et sélecteurs de revert 4–36 octets sans mise à jour de `mload(0x40)` | Layer 3 (`BlockPatchRule`) | **30 – 75 gas / hachage ou revert** |
| **G6** | **Décodage calldata eager** (copie en mémoire de tous les paramètres avant exécution) | Décodage `calldataload` paresseux par vue (`CalldataSlice`) + vérification de nettoyage (`calldataload(off) == and(calldataload(off), mask)`) uniquement sur les paramètres utilisés | Layer 2 + Layer 3 | **60 – 250 gas / appel** |
| **G7** | **Dispatch linéaire $O(N)$** sur les contrats à > 8 fonctions | Activation par défaut de `SelectorDispatchTree` ($O(\log N)$) dès $N \ge 6$ | Layer 3 (`Selector.lean`) | **50 – 300 gas / appel** |

#### Boucle de Superoptimisation Autonome (`maxwell` / The Maxwell Gate)
1. **Minage (`ShimArena`)** : Extrait des traces 4-voies les sous-arbres IR/Yul où $\text{Gas}_{\text{Verity}} > \text{Gas}_{\text{solc}}$ ou $\text{Gas}_{\text{Solady}}$.
2. **Conjecture & Pré-filtre (`turbo-lean fast-check`)** : Teste chaque règle candidate $(L \Rightarrow R \text{ if } P)$ sur `100 000` états aléatoires en `< 1 ms`. Tout contre-exemple brûle immédiatement la branche (`p = 0`).
3. **Certification Parallèle (`research-governor`)** : Distribue 1 règle = 1 fichier `.lean` sur des workers isolés qui prouvent :
   - `preserves_eval` : égalité `ObsEquiv` sur `EvmYul/Yul/Interpreter.lean` ;
   - `improves_cost` : inégalité stricte/large sur `EvmYul/Yul/GasInterpreter.lean` pour tout `Fork ≥ Cancun`.
4. **Promotion (`governor_accept_gate_sound`)** : Vérifie `0 sorryAx`, `0 native_decide`, `0 vacuous_specs` via `turbo-lean audit-spec` et ajoute la règle à `CertifiedPatchPack`.

---

### 2.4 Moteur de Découverte de Bugs dans `solc` (Compiler Bug Discovery Engine)

Lorsque le contrat importé possède un témoin `CertifiedContractTranslationWitness` (`SolcoreBridge`) et que les voies **B (Verity Layer 1)**, **C (`EVMYulLean 2.0` Yul)** et **D (Verity EVM)** concordent mais divergent de **A (`solc` Legacy ou `solc --via-ir --optimize`)** sur une observation sémantique (`status`, `returndata`, `logs`, `storage`, `transient`), le système isole une **erreur de compilation candidate dans `solc`** :

1. **Classes de bugs `solc` ciblées** :
   - **Aliasing mémoire/stockage dans l'optimiseur Yul (`LoadResolver`, `RedundantStoreEliminator`, `UnusedStoreEliminator`)** : élimination erronée d'un `mstore`/`sstore` ou réutilisation d'un `sload` périmé après un appel ou un `keccak256` dont les bornes mémoire chevauchent une écriture dynamique.
   - **Réordonnancement d'effets de bord (`ExpressionSplitter` / `CommonSubexpressionEliminator`)** : altération de l'ordre d'évaluation droite-à-gauche des arguments Yul en présence d'appels modifiant l'état ou lisant `returndatasize()`.
   - **Bits de poids fort sales (`Dirty High Bits`)** : omission d'un `and(..., mask)` ou `signextend` après arithmétique `unchecked`, chargement `mload`/`sload` packé ou retour d'appel externe sur `uint8..uint128` / `bytesN` / `bool`.
   - **Chevauchement ABI head/tail et corruption du pointeur libre `0x40`** : écrasement de mémoire lors de `abi.encode` / `abi.decode` de tuples dynamiques imbriqués ou de tableaux `bytes[]` en calldata/storage.
2. **Arbre de Triage Automatique & Delta-Debugging (`verity-solc-reduce`)** :
   - Vérifie d'abord que le programme n'utilise aucun comportement non spécifié et compare `solc --optimize` contre `solc --no-optimize` et `solc --via-ir --no-optimize` pour localiser exactement l'étape fautive dans `solc` (codegen Legacy vs abaissement IR vs étape précise de séquence `--yul-optimizations`).
   - Réduit automatiquement le contrat Solidity et la séquence d'appels (suppression de fonctions, d'instructions et de champs d'état tout en préservant la divergence `Obs(Verity) ≠ Obs(solc)`) jusqu'à un **PoC minimal de < 30 lignes** prêt pour rapport upstream `ethereum/solidity`.
