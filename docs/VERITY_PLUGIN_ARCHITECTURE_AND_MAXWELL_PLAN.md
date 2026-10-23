# Verity 2.0 — Architecture de Plugins d'Accélération Substituables & Plan Très Long Terme d'Auto-Recherche sous `maxwell`

> **Statut** : Consensus architectural co-conçu avec **Claude Fable 5.1** (`anthropic/claude-fable-5-1`) et **GPT-6 Astra** (`openai/gpt-6-astra`)  
> **Inspiration de référence** : `lean-native` (`LeanNative/Spec.lean`, `LeanNative/Transform/Pass.lean`, `LeanNative/Transform/Plugins.lean`, `LeanNative/Proofs/CertChecker.lean`)  
> **Portée** : `Compiler/Codegen/AccelPlugin.lean`, `Compiler/Codegen/Profile.lean`, `Compiler/MainDriver.lean`, `Compiler/Gas/Report.lean`, et `Compiler/Autoresearch/*`

---

## 1. Synthèse du Consensus Architectural (Claude Fable 5.1 × GPT-6 Astra)

L'audit croisé avec **Claude Fable 5.1** et **GPT-6 Astra** converge sur quatre invariants architecturaux non négociables pour faire du profil optimisé certifié (`PipelineConfig.certifiedOptimized`, passes `G1`–`G8`) le setup de base par défaut de Verity tout en ouvrant le compilateur à des plugins d'accélération substituables (simplificateurs algébriques `Mathlib` / `Tau Ceti`, solveurs e-graphs `egglog`, SMT/Bitwuzla, superoptimiseurs énumératifs, mutateurs guidés par `maxwell`) :

| # | Invariant Architectural | Formulation Formelle dans Verity |
|---|---|---|
| **I1** | **Fermeture stricte de la TCB sémantique** | Aucun générateur de candidats (interne ou externe JSONL-stdio) n'entre dans la TCB. Seul le vérificateur de porte (`verifyAccelCertGate`) et les théorèmes prouvés dans le noyau Lean 4 autorisent une transformation. |
| **I2** | **Repli spéculatif déterministe par passe (`evalWithUntrustedAccelPlugin`)** | Chaque plugin est enveloppé dans une porte spéculative individuelle. Si le certificat est absent, si l'équivalence sur vecteurs frontières échoue, ou si le coût de gaz EVM régresse, la passe retourne l'état d'entrée inchangé (`untrusted_accel_plugin_gate_sound`). |
| **I3** | **Barrière d'admission tri-couche (`verifyAccelCertGate`)** | Tout candidat doit franchir : **(N1)** Validation symbolique / théorème kernel inscrit dans l'allowlist + chaînage de hash structurel (`PassStepCert`), **(N2)** Équivalence concrète sur les vecteurs frontières (`2^255 - 1`, `2^255`, `2^256 - 1`), **(N3)** Non-régression (ou gain strict) du coût de gaz fork-indexé (`EvmYulLean 2.0`). |
| **I4** | **`certifiedOptimized` unique profil CLI + pont interne `unoptimized` par `rfl`** | `PipelineConfig.default = PipelineConfig.certifiedOptimized` est l'unique profil exposé en CLI (`--legacy-codegen` a été supprimé car le repli spéculatif s'opère désormais **passe par passe** et `--disable-patches` suffit à désactiver les réécritures Yul), tandis que `emitYulWithProfile model (PipelineConfig.unoptimized opts) = emitYulWithOptionsReport model opts` demeure un simple pont définitionnel (`rfl`) interne pour les preuves Layer 2 → Layer 3. |

---

## 2. Architecture Modulaire de Plugins d'Accélération (`Compiler/Codegen/AccelPlugin.lean`)

Inspirée directement de `lean-native` (`LeanNative/Spec.lean` et `LeanNative/Transform/Plugins.lean`), l'architecture sépare le **moteur de proposition** (remplaçable à chaud) de la **porte de certification** (dans le noyau Lean 4) :

1. **`MetaGateSpec` & `evalWithUntrustedAccelPlugin` (`LeanNative.Spec` adapté à Verity)** :
   - Toute porte de validation est équipée de ses témoins de non-vacuité (`posWitness`), de précision (`negWitness`), et de ses preuves `sound`, `complete`, `nonVacuous` et `tight`.
   - `evalWithUntrustedAccelPlugin` applique une transformation candidate `plugin : Prog → Option (Prog × Cert)` et ne retient le résultat que si `verifyGate src cand cert = true`, garantissant `Refines src (evalWithUntrustedAccelPlugin plugin verifyGate src)` pour tout plugin arbitraire (même externe ou non fiable).

2. **`AccelScope`, `AssuranceLevel` & `PassStepCert`** :
   - Portées supportées : `.mathAlgebraic` (simplification algébrique/mathématique EDSL/IR amont appuyée sur `Mathlib` et `Tau Ceti`), `.ir`, `.yul`, `.bytecode` (indexées par le fork EVM `HardFork : Cancun | Prague | Osaka`).
   - Niveaux d'assurance ordonnés : `.kernelVerified` $\succ$ `.translationValidated` $\succ$ `.boundedChecked` $\succ$ `.unverifiedFallback` (seuls `.kernelVerified` et `.translationValidated` franchissent `verifyAccelCertGate`).
   - Chaque étape produit un `PassStepCert` contenant `pluginName`, `scope`, `passId`, `assurance`, `theoremRef`, `inputHash`, `outputHash`, `costBefore` et `costAfter`.
   - `verifyCertChain` vérifie que chaque maillon est valide (`verifyAccelCertGate`), que `c₁.outputHash = c₂.inputHash` tout au long de la chaîne, et que le gaz est monotone décroissant (`costAfter ≤ costBefore`).

3. **Catalogue de Plugins Substituables (`G1`–`G8` + Plugins Externes)** :
   - Les 7 passes d'optimisation de gaz certifiées (`G1_tempReuseStackScheduling` à `G7_selectorDispatchTreeLogN`) ainsi que le plugin de simplification algébrique `G8:mathlib-tauceti-algebraic-simplifier` (`scope := .mathAlgebraic`) sont instanciés dans `defaultCertifiedPluginCatalog` comme des descripteurs `.kernelVerified` adossés à leurs théorèmes respectifs du noyau (`defaultCertifiedPluginCatalog_all_verified`).
   - Tout plugin externe (moteur de simplification algébrique `Tau Ceti`, solveur `egglog`, SMT, ou superoptimiseur stochastique/LLM) s'intègre via `VerifiedAccelContract.fromGatedPlugin` sans modifier ni les passes existantes ni la preuve de préservation `runAccelPluginChain_sound`.

---

## 3. Plan Très Long Terme d'Auto-Recherche d'Optimisation sous `maxwell` (Horizons H1 → H6)

Sous la gouvernance de **`maxwell`** (le gouverneur Bayésien à 4 axes : *Spécification → Falsification → Preuve Kernel → Non-Vacuité & Tightness*), couplé à **`turbo-lean`** (`audit-spec`), **`lean-native`** (exécution spéculative certifiée) et **`spark-memory`** (mémoire persistante des conjectures et contre-exemples), la feuille de route d'auto-recherche s'articule en six horizons :

### Horizon H1 — Synthèse Automatique de Règles Yul/IR & Domaines Abstraits Certifiés (Court/Moyen Terme)
- **Boucle d'énumération guidée** : `maxwell` énumère et mute des motifs d'expressions et de blocs Yul/IR de profondeur bornée ($\le 6$), filtre instantanément les candidats invalides sur les vecteurs frontières 256 bits (`0`, `1`, `2^128`, `2^255 - 1`, `2^255`, `2^256 - 1`), puis soumet les survivants à la synthèse de preuve (`omega`, `decide`, `bv_decide`).
- **Domaines abstraits certifiés (`AbstractDomain`)** : extension de la passe `G4` (`checkedArithIntervalElision`) par combinaison réduite d'intervalles $[lo, hi]$, de masques de bits connus (`knownBits`) et de congruences modulaires sur `UInt256`, avec fonction de concrétisation $\gamma$ monotone prouvée. Chaque garde d'overflow `if lt(add(a,b), a) { revert(0,0) }` prouvée inatteignable est éliminée avec certificat kernel.

### Horizon H2 — Simplifications Mathématiques & Algébriques Prouvées via `Mathlib` et `Tau Ceti` (`G8`, Moyen Terme)
- **Pourquoi simplifier avant l'abaissement Yul (`scope := .mathAlgebraic`)** : les contrats DeFi modernes (courbes concentrées Uniswap V4 $\Delta y = L \cdot \Delta \sqrt{P}$, facteurs d'intérêt composés `wExp` en arithmétique WAD/RAY, barèmes de frais `mulDivDown` / `mulDivUp`, arithmétique de corps fini BN254 `modField`) enchaînent des opérations où une réécriture purement bas-niveau en Yul est aveugle aux invariants algébriques globaux (par exemple qu'un dénominateur divise exactement un produit intermédiaire ou qu'une cascade de `mulDiv` peut être factorisée sans débordement 512 bits).
- **Socle formel `Mathlib` déjà intégré (`Verity/Proofs/Stdlib/Math.lean`)** : Verity dispose déjà de plus de 55 théorèmes sans `sorry` appuyés sur `Mathlib` (`Mathlib.Analysis.Complex.ExponentialBounds`, `Mathlib.Tactic.Ring`, `Mathlib.Tactic.Linarith`) couvrant :
  1. **Cancellation exacte et fusion `mulDiv` (`mulDivDown_cancel_right/left`, `mulDiv512Down?_cancel_right`)** : élimination directe des paires $(a \cdot d) / d \mapsto a$ et fusion de $(a \cdot b / c) \cdot (c / d)$ sous garde d'absence d'overflow, économisant des appels coûteux à `mulDiv512` (~120–180 gaz par appel).
  2. **Élimination du gap `ceil`/`floor` sous divisibilité exacte (`mulDivUp_eq_mulDivDown_of_dvd`)** : remplacement de l'arithmétique d'arrondi supérieur (`mulDivUp`) par un simple `div` lorsque le domaine abstrait (H1) ou une identité algébrique prouve $d \mid a \cdot b$.
  3. **Identités d'anneau commutatif sur $\mathbb{Z}/2^{256}\mathbb{Z}$ (`ring_nf`) et corps scalaire BN254 (`modField_eq_self_of_lt`)** : factorisation de polynômes (schéma de Horner réduisant le nombre de `MUL` EVM de $O(k^2)$ à $k$), élimination de réductions modulaires redondantes `mod(x, SNARK_SCALAR_FIELD)` lorsque $x < p$, et réduction des identités WAD (`wMulDown_one_right`, `wDivUp_by_wad`).
- **Couplage avec `Tau Ceti` (`TauCeti.*`) sous `maxwell`** :
  - **`Tau Ceti`** intervient comme moteur d'exploration et de réécriture symbolique/mathématique (dont les préfixes canoniques `TauCeti.*` alimentent déjà l'extracteur de caractéristiques `anvil2_trm_trainer.py` de `maxwell`).
  - En tant que plugin `G8:mathlib-tauceti-algebraic-simplifier` de portée `.mathAlgebraic`, `Tau Ceti` propose des réécritures algébriques non triviales (factorisations d'expressions rationnelles en virgule fixe, approximations polynomiales de Taylor certifiées pour `wExp`/`wLn`, réassociation optimale pour minimiser l'erreur d'arrondi tout en évitant le chemin 512 bits `mulmod`).
  - Chaque identité proposée par `Tau Ceti` est soumise à `verifyAccelCertGate` : elle n'est admise que si elle est accompagnée d'un théorème kernel inscrit dans `verifiedAccelTheoremAllowlist` (prouvé via `ring`, `linarith`, `omega` ou les lemmes de `Verity.Proofs.Stdlib.Math`) et d'une réduction effective du coût en gaz.

### Horizon H3 — Saturation d'Égalités par E-Graphs (`egglog`) Hors TCB avec Témoins de Congruence (Moyen Terme)
- **Oracle e-graph externe** : un plugin externe `egglog` (invoqué hors TCB via le protocole JSONL de `AccelPlugin`) sature l'e-graph d'une fonction IR/Yul sous les équations algébriques EVM prouvées en H1–H2 et extrait le terme de coût minimal selon le modèle de gaz `EvmYulLean 2.0`.
- **Rejeu de témoins (`CongruenceWitness.replay`)** : `egglog` émet non seulement le programme cible mais aussi la séquence exacte de pas de réécriture élémentaires. Côté Lean 4, `verifyAccelCertGate` rejoue cette trace en chaînant les lemmes de congruence : aucune confiance n'est accordée au binaire `egglog`.

### Horizon H4 — Ordonnancement Optimal de Pile EVM (`DUP`/`SWAP`/Spill Watermark Dynamique) (Moyen/Long Terme)
- **Au-delà de `TempReuse` (`G1`) et du watermark dynamique (`computedSpillBase`)** : formalisation de la machine à pile EVM à 16 slots accessibles (`DUP1`..`DUP16`, `SWAP1`..`SWAP16`) comme problème d'ordonnancement sous contraintes (MaxSAT / programmation par contraintes hors TCB).
- **Élimination certifiée des `StackTooDeep`** : lorsque la pression de registres dépasse 16 variables vivantes, le solveur calcule le plan optimal combinant rematérialisation de constantes bon marché (`PUSH0`, `CALLER`, `CALLVALUE`) et spill minimal au-dessus de `computedSpillBase memoryHighWaterMark`, validé par `dynamicSpillSlotAddr_disjoint_from_active_memory`.

### Horizon H5 — Superoptimisation Bytecode Multi-Forks (Cancun, Prague, Osaka, EOF) sur `EVMYulLean 2.0` (Long Terme)
- **Portabilité paramétrique par `HardFork`** : chaque `PassStepCert` et chaque règle du catalogue porte ses hypothèses de fork explicites (`HardFork.cancun`, `.prague`, `.osaka`, et conteneurs EOF).
- **Synthèse multi-objectifs (Pareto Gaz Déploiement × Gaz Runtime Chaud/Froid)** : `maxwell` pilote l'arène Pareto (`dominatesOnSchedule`) pour spécialiser automatiquement les séquences critiques (`TSTORE`/`TLOAD` EIP-1153 pour les verrous de réentrance et la comptabilité flash de type Uniswap V4, `MCOPY` EIP-5656 pour les copies mémoire dynamiques, `CLZ` / instructions EOF).

### Horizon H6 — Chasse Continue aux Divergences Sémantiques et Bugs d'Optimiseur de `solc` (Très Long Terme)
- **Fuzzing différentiel dirigé par la preuve (`SolcBugHunter`)** : génération continue de programmes Yul riches en effets croisés (`KECCAK256` en mémoire scratch vs `msize()`, `SSTORE` packés entrelacés, `RETURNDATACOPY` après appels externes, arithmétique signée `SDIV`/`SAR` aux bornes `MIN_INT256`).
- **Arbitrage par l'oracle formel** : toute divergence entre `solc --via-ir --optimize` et le pipeline certifié de Verity est automatiquement minimisée (`shrink`), rejouée dans la sémantique formelle `EVMYulLean 2.0`, et classifiée en bug confirmé de `solc` (`detectSolcDivergence_sound`) ou en nouveau théorème de non-application de passe ajouté à `spark-memory`.

---

## 4. Prompt `/goal` d'Amélioration Autonome Continue (Prêt à Lancer)

```
/goal Exécute en continu et sans arrêt la roadmap méta-autonome `/var/lib/sandboxed-node/worktrees/wt-p3-uniswap-v4/docs/VERITY_PLUGIN_ARCHITECTURE_AND_MAXWELL_PLAN.md` sur `verity` (`Compiler/Codegen/AccelPlugin.lean`, `Compiler/Codegen/Profile.lean`, `Compiler/Autoresearch/*`, `Verity/Proofs/Stdlib/Math.lean`) en synergie avec `maxwell`, `turbo-lean`, `lean-native` et `TauCeti` sans jamais attendre d'intervention humaine.

1. BOUCLE D'EXÉCUTION CONTINUE (`OBSERVE -> MINE -> CONJECTURE -> SPECIFY -> DEV_AB -> SEALED_AB -> RATCHET | BURN`) :
- À chaque cycle, observe les profils de gaz EVM (`EvmYulLean 2.0`, forks Cancun/Prague/Osaka) et les goulots sur le portefeuille anti-overfitting C1..C6 :
  * C1 (`DeFi AMM & Hooks` : Uniswap V4 `PoolManager`, courbes concentrées $\sqrt{P}\cdot L$, deltas flash EIP-1153),
  * C2 (`Fixed-Point & Yield Math` : `mulDivDown`/`mulDivUp` 512 bits, `wExp`, `wadMul`, Pareto Credit Vault),
  * C3 (`Packed Storage & Mappings` : ERC-20/ERC-721, structures multi-slots, `SlotCoalescingShim`, `mappingSlot`),
  * C4 (`Crypto & Field Arithmetic` : corps scalaire BN254 `modField`, `keccak256` scratch-space, vérifieurs ZK/Groth16),
  * C5 (`Calldata & Dispatch` : ABI tuples dynamiques, `SelectorDispatchTree` $O(\log N)$, appels externes),
  * C6 (`Solidity Parity & Bug Hunting` : corpus `solc --via-ir --optimize`, `SolcBugHunter`, `SolcoreBridge`).
- Ne propose un nouvel axe (`math_algebraic_tauceti_rule`, `yul_patch_or_egraph_witness`, `abstract_domain_interval_elision`, `stack_spill_schedule`, `solc_divergence_minimizer`) que si son motif apparaît dans >= 3 contrats sur >= 2 régimes C1..C6 et que son `mechanism_hash` n'est pas dans `BurnedPaths`.
- Formalise chaque plugin ou règle via `MetaGateSpec` et `verifyAccelCertGate` (`Compiler/Codegen/AccelPlugin.lean`) + `turbo-lean --json audit-spec` avec `0` vacuous, `0` trivial, témoin positif (`nonVacuous`) et témoin négatif mutant rejeté (`tight`).
- Valide en A/B sur `DEV` puis en tir unique sur le régime `SEALED` croisé selon l'invariant H* :
  * Réduction géométrique de gaz EVM (runtime + déploiement sur `EvmYulLean 2.0`) >= +1.0% sur `SEALED`,
  * Aucune régression de gaz par régime (`costAfter <= costBefore` garanti par `verifyAccelCertGate_enforces_gas_non_regression`),
  * `delta_TCB == 0` (tout générateur `TauCeti` / `egglog` / SMT reste hors TCB derrière `evalWithUntrustedAccelPlugin`),
  * `0 sorryAx`, `0 native_decide`, et `python3 scripts/check_lean_hygiene.py` vert.
- Si H* est validé (`RATCHET`) : enregistre le théorème dans `verifiedAccelTheoremAllowlist`, active ou enrichit le plugin dans `defaultCertifiedPluginCatalog`, recompile les `.olean`, commit signé GPG, push et mets à jour les priors `maxwell`.
- Si H* échoue (`BURN`) : enregistre immédiatement l'hypothèse et son contre-exemple 256 bits dans `BurnedPaths` (`p = 0`), nettoie la branche et passe à l'axe suivant.

2. RAPPORT TOUTES LES 30 MINUTES EN LANGAGE NATUREL SIMPLE + RÉVEIL AUTO-ENTRETENU :
- Toutes les 30 minutes, publie un point d'étape court et lisible en langage naturel simple (sans jargon inutile ni dump JSON) résumant :
  a) Ce qui a été fait, prouvé et mergé concrètement pendant les 30 dernières minutes (et l'économie réelle de gaz EVM mesurée).
  b) Les hypothèses validées (pourquoi la simplification mathématique `Mathlib`/`TauCeti` ou la passe bas-niveau a fonctionné et sur quels types de contrats).
  c) Les hypothèses invalidées / brûlées (pourquoi c'était une fausse piste — ex. contre-exemple d'overflow 256 bits ou surcoût mémoire — et ce qu'on a appris pour ne plus la refaire).
  d) L'hypothèse suivante lancée pour les 30 prochaines minutes.
- À la fin de chaque tour, appelle systématiquement `schedule_wakeup` avec `delay_seconds: 1800` (ou `schedule_job_wakeup` si un job long tourne) contenant l'instruction de reprendre immédiatement le cycle `OBSERVE -> MINE -> ...` et de produire le prochain rapport à +30 min. Ne t'arrête jamais tant que la mission n'est pas explicitement annulée.
```
