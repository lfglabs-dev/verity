"""Paired re-import check: an unrelated state variable must not change an imported model (#2830).

For each case the harness imports the target functions twice, on each listed profile:

* **base**: the fixture as written;
* **variant**: the same fixture with one unrelated `uint256` state variable and one unused
  external function appended at the end of the target contract's body.

Normalization. Appending after every existing declaration of the most-derived contract
leaves solc's storage layout of the original variables unchanged, and solc's own
`storageLayout` output is checked to prove it for every case: each original variable keeps
its slot, offset and type, and the probe takes a fresh slot after all of them. The unused
function is not in the import list. The only expected difference in the generated
`CompilationModel` is therefore the probe's storage field, which is removed before comparing;
everything else (functions, events, errors, externals, constructor, remaining fields) must
render identically. If the probe would move or overlap an original variable, the case fails
as unsound instead of being compared.

Every non-control case must declare `base_count` state variables in its base (default 1,
counted from solc's AST the way the importer counts them, constants and immutables included),
so the probe moves the count from `base_count` to `base_count + 1` (`1 -> 2` across the
`stateVars.size > 1` gates of #2830, or `0 -> 1` when `base_count=0` is set explicitly; note
that the five separate `stateVars.isEmpty` 0-slot slice boundaries in `lowerInterfaceStaticCall`,
`bindCallArgs`, `admittedRequireInterfaceCall?` and `lowerRoot` are locked by their own
rejection suites outside #2830). Lean prints each normalized model with its length, and a model
that does not arrive whole on one line is a harness error, as is a failing side without a
`[solidity-import]` diagnostic.

A case passes when both sides import with identical normalized models, or both sides reject
with the same diagnostic. It fails when only one side imports (an admission discrepancy) or
when both import with different models (a model discrepancy). A case rejected on every profile
fails unless it declares `expect='same-rejection'`: a construct that must stay rejected,
with the same diagnostic, whatever the state-variable count.

Negative controls run with every invocation (unless `--only` filters them out):

* `control-probe-first` inserts the probe *before* the original variables. The layout check
  must refuse it, so a slot-shifting normalization can never be compared as if it were sound.
* `control-model-change` additionally changes a literal in the variant's function body. The
  comparison must report a model discrepancy, proving that differences are detected.

Cases on `EXPECTED_DISCREPANCIES` are importer behaviour known to depend on the state-variable
count on `main`. They are not required to pass: the harness requires the listed discrepancy
kind to be observed, and fails when it disappears so the entry is removed with its fix.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path.cwd().resolve()
SOLC = ROOT / '.lake/solidity-import/solc-0.8.34'
PROBE = 'verityStateCountProbe'
PROBE_FUNCTION = 'verityStateCountProbeUnused'
PROFILES = {
    'legacy': '{ evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none" }',
    'ir': '{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }',
}
HEADER = '// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'


def inline(name, body, functions, contract='C', **options):
    """A one-file case whose contract text is given inline."""
    return {'name': name, 'files': {'Fixture.sol': HEADER + body}, 'entry': 'Fixture.sol',
            'contract': contract, 'functions': functions, **options}


def fixture(name, path, contract, functions, **options):
    """A case importing a checked-in fixture; the `.sol` files of its directory are copied."""
    return {'name': name, 'directory': str(Path(path).parent), 'entry': Path(path).name,
            'contract': contract, 'functions': functions, **options}


def solidity_only(directory, names):
    return [n for n in names if not n.endswith('.sol') and not (Path(directory) / n).is_dir()]


# Minimal controls: each construct imports on main on both profiles. Every non-control case
# declares exactly one state variable (the importer's count includes constants and immutables),
# so the probe moves the count from 1 to 2 and crosses the `stateVars.size > 1` gates.
CASES = [
    inline('scalar-storage', '''contract C {
    uint256 private total;

    function bump(uint256 x) external returns (uint256) {
        total = total + x;
        return total;
    }
}
''', ['bump(uint256)']),
    inline('mapping-and-event', '''contract C {
    mapping(address => uint256) private balances;
    event Moved(address indexed who, uint256 amount);

    function credit(address who, uint256 amount) external returns (uint256) {
        balances[who] += amount;
        emit Moved(who, amount);
        return balances[who];
    }
}
''', ['credit(address,uint256)']),
    inline('require-message-helper', '''contract C {
    uint256 private stored;
    error TooLarge(uint256 value);

    function check(uint256 n) internal pure returns (uint256) {
        require(n != 7, "seven");
        return n * 2;
    }

    function run(uint256 x) external returns (uint256) {
        if (x > 1000) revert TooLarge(x);
        stored = check(x);
        return stored;
    }
}
''', ['run(uint256)']),
    inline('yul-bool-literal', '''contract C {
    uint256 private total;

    function flag(uint256 x) external returns (bool r) {
        total = x;
        assembly { r := true }
    }
}
''', ['flag(uint256)']),
    inline('yul-if', '''contract C {
    uint256 private total;

    function clamp(uint256 x) external returns (uint256 r) {
        total = x;
        assembly { r := x if gt(x, 10) { r := 10 } }
    }
}
''', ['clamp(uint256)']),
    inline('memory-struct-locals', '''contract C {
    struct Pair {
        uint256 a;
        bool flag;
    }

    uint256 private total;

    function split(uint256 x) internal pure returns (Pair memory p, uint256 k) {
        p.a = x + 1;
        p.flag = x > 4;
        k = x * 2;
    }

    function make(uint256 x) internal pure returns (uint256, Pair memory) {
        return (x + 3, Pair(x, true));
    }

    function run(uint256 x) external returns (uint256) {
        total = x;
        (Pair memory p, uint256 k) = split(x);
        (uint256 j, Pair memory q) = make(x);
        Pair memory z;
        if (q.flag) z.a = j;
        return p.flag ? p.a + k + z.a : q.a + z.a;
    }
}
''', ['run(uint256)']),
    inline('storage-mapping-argument', '''contract C {
    struct Book {
        uint256 total;
        mapping(address => uint256) bal;
    }

    Book private book;

    function credit(mapping(address => uint256) storage m, address who, uint256 v) internal returns (uint256) {
        m[who] += v;
        return m[who];
    }

    function run(address who, uint256 v) external returns (uint256) {
        book.total = v;
        uint256 r = credit(book.bal, who, v);
        return r + book.bal[who];
    }
}
''', ['run(address,uint256)']),
    inline('encode-call-bytes-parameter', '''interface ISink {
    function put(uint256 tag, bytes calldata data) external;
}

contract C {
    uint256 private total;

    function run(uint256 x, bytes calldata b) external returns (bytes32) {
        total = x;
        return keccak256(abi.encodeCall(ISink.put, (x, b)));
    }
}
''', ['run(uint256,bytes)']),
    inline('event-helper-prelude', '''contract C {
    uint256 private total;
    event Pair(uint256 indexed a, uint256 indexed b);

    function mix(uint256 a) internal pure returns (uint256 r) {
        r = a;
        r = r ^ 0x55;
    }

    function run(uint256 x, uint256 y) external {
        total = x;
        emit Pair(mix(x), mix(y));
    }
}
''', ['run(uint256,uint256)']),
    inline('conditional-modifier', '''contract C {
    uint256 private total;

    modifier when(bool on) {
        if (on) {
            _;
        }
    }

    function run(uint256 x) external when(x > 1) returns (uint256) {
        total = x;
        return x;
    }
}
''', ['run(uint256)']),
    # On an internal helper the substitution of #2846 is not available: still the same
    # located rejection whatever the state-variable count.
    inline('conditional-modifier-helper', '''contract C {
    uint256 private total;

    modifier when(bool on) {
        if (on) {
            _;
        }
    }

    function store(uint256 x) internal when(x > 1) {
        total = x;
    }

    function run(uint256 x) external returns (uint256) {
        store(x);
        return x;
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    inline('forwarded-tuple-modifiers', '''contract C {
    uint256 private total;

    modifier outerMod() {
        total = total * 10 + 1;
        _;
        total = total * 10 + 9;
    }

    modifier helperMod() {
        total = total * 10 + 2;
        _;
        total = total * 10 + 8;
    }

    function _pair(uint256 x) private helperMod returns (bool ok, bytes memory data) {
        total = total * 10 + 3;
        if (x != 0) {
            ok = true;
            data = abi.encodePacked(total, uint16(x));
        }
    }

    function run(uint256 x) external outerMod returns (bool ok, bytes memory data) {
        return _pair(x);
    }
}
''', ['run(uint256)']),
    inline('forwarded-tuple-substituted-modifier', '''contract C {
    uint256 private total;

    modifier twice() {
        total += 1;
        _;
        total += 10;
        _;
    }

    modifier when(bool on) {
        if (on) {
            _;
        }
    }

    function _pair(uint256 x) private returns (bool ok, bytes memory data) {
        total += x;
        ok = (x != 0);
        data = abi.encode(total);
    }

    function run(uint256 x) external twice when((total + x) % 2 == 1) returns (bool, bytes memory) {
        return _pair(x);
    }
}
''', ['run(uint256)']),
    inline('unchecked-block-declaration', '''contract C {
    uint256 private total;

    function h(uint256 a) internal pure returns (uint256 r) {
        uint256 v = a;
        unchecked {
            uint256 v = a - 1;
            if (v == 0) return 100;
        }
        assembly {
            r := v
        }
    }

    function run(uint256 x) external returns (uint256) {
        total = x;
        return h(x);
    }
}
''', ['run(uint256)']),
    # Contract creation and `try this.f()` reject at the construct in every contract: the
    # multi-slot lowerings were a staticcall to this contract and an oracle call success bit.
    inline('contract-creation', '''contract Child {
    constructor(uint256 a) { require(a != 0); }
}

contract C {
    uint256 private total;

    function make(uint256 x) external returns (uint256) {
        total = x;
        return uint256(uint160(address(new Child(x))));
    }
}
''', ['make(uint256)'], expect='same-rejection'),
    inline('self-try-call', '''contract C {
    uint256 private total;

    function poke(uint256 x) external {
        total = x;
        require(x != 0);
    }

    function run(uint256 x) external returns (uint256 r) {
        try this.poke(x) { r = 1; } catch { r = 2; }
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    # Conditional ABI encoding argument (#2830).
    inline('encoding-conditional', '''contract C {
    uint256 private total;

    function hashChoice(uint256 x, bool c) external returns (bytes32) {
        total = x;
        return keccak256(abi.encode(c ? x : total));
    }
}
''', ['hashChoice(uint256,bool)']),
    inline('root-array-return', '''contract C {
    uint256 private total;

    function pair(uint256 x) external returns (uint256[] memory r) {
        total = x;
        r = new uint256[](2);
        r[0] = x;
        r[1] = total;
    }
}
''', ['pair(uint256)']),
    fixture('fixture-storage-void-sequence', 'Contracts/SolidityImportSmoke/StorageVoidSequence.sol',
            'SequenceFixture', ['change(uint256)', 'fail()', 'read()']),
    fixture('fixture-interface-static-call', 'Contracts/SolidityImportSmoke/InterfaceStaticCallOneSlot.sol',
            'InterfaceStaticCallOneSlot', [
                'peerQuote(address,address)', 'typedReceiver(IWordFeed,uint256)',
                'narrowQuote(address,uint128,int256,bytes4)', 'ownerWord(address)',
                'smallWord(address)', 'convertedArgument(address,uint8)',
                'returned(address,uint256)', 'leftOperand(address,uint256)',
                'rightOperand(address,uint256)', 'compound(address,uint256)',
                'mappingTarget(address,uint256)', 'conditional(address,uint256)',
                'nestedReceiver(address,uint256)', 'helperReturn(address,uint256)',
                'negatedCondition(address,address)', 'equalityRequire(address,uint256)',
                'helperArguments(address,uint256)', 'discardedOwner(address)',
                'discardedSmall(address)', 'rateWord(address)', 'discardedRate(address)']),
    fixture('fixture-storage-mapping-argument', 'Contracts/SolidityImportSmoke/StorageMappingArgumentOneSlot.sol',
            'StorageMappingArgumentOneSlot', [
                'deposit(uint256,address,uint256)', 'forwarded(uint256,address,uint256)',
                'cleared(uint256,address)', 'aliased(uint256,address)', 'shifted(uint256,uint256,int256)',
                'entry(uint256,uint256,uint256)', 'signedKey(uint256,int8,uint256)',
                'packedEntry(uint256,uint256,uint128,uint64)',
                'pointer(uint256,address,uint256)', 'keyOrder(uint256,address)', 'slotOfMember(uint256)',
                'rawSlot(address,uint256)', 'rawSlotOf()']),
    fixture('fixture-root-array-return', 'Contracts/SolidityImportSmoke/RootArrayReturnOneSlot.sol',
            'RootArrayReturnOneSlot', [
                'loadSlots(«bytes32[]»)', 'loadTransientSlots(«bytes32[]»)', 'loadRange(bytes32,uint256)',
                'revertedWord(uint256)', 'copied(«uint256[]»)', 'narrowCopied(«uint8[]»)', 'fromStorage()', 'built(uint256)']),
    fixture('fixture-encode-call-bytes', 'Contracts/SolidityImportSmoke/EncodeCallBytesOneSlot.sol',
            'EncodeCallBytesOneSlot', [
                'literalEmpty()', 'literalLong()', 'memoryArg(uint256)', 'memoryLength(uint256)',
                'helperArg(uint256)', 'calldataArg(bytes)', 'storageArg(uint256)',
                'staticSiblings(uint256,bytes,address)', 'dynamicSiblings(bytes,uint256,uint256)',
                'helperRevert(uint256,uint256)', 'returned(uint256)']),
    fixture('fixture-event-helper-prelude', 'Contracts/SolidityImportSmoke/EventHelperPreludeOneSlot.sol',
            'EventHelperPreludeOneSlot', [
                'helperTwice(uint256,uint256)', 'helperAndLocal(uint256)', 'storedPair(uint256,uint256)',
                'guardedPair(uint256,uint256)', 'assembledMixed(uint256,uint256)']),
    fixture('fixture-unchecked-block-declaration',
            'Contracts/SolidityImportSmoke/UncheckedBlockDeclarationOneSlot.sol',
            'UncheckedBlockDeclarationOneSlot', [
                'runBumped(uint256)', 'runCheckedAfter(uint256,uint256)', 'runTwoDeclarations(uint256)',
                'runRedeclared(uint256)', 'runShadowedLocal(uint256)', 'runShadowedConstant(uint256)']),
    fixture('fixture-helper-branch-scope', 'Contracts/SolidityImportSmoke/HelperBranchScopeOneSlot.sol',
            'HelperBranchScopeOneSlot', [
                'runThenDeclares(uint256)', 'runElseDeclares(uint256)', 'runNestedDeclares(uint256)',
                'runOuterBranchDeclares(uint256)', 'runShadowsConstant(uint256)', 'runAssignsOuter(uint256)',
                'runUncheckedBranch(uint256)', 'runBlockDeclaresString(uint256)',
                'runBlockDeclaresArray(uint256)']),
    fixture('fixture-effect-core', 'Contracts/SolidityImportSmoke/EffectCoreOneSlot.sol',
            'EffectCoreOneSlot', [
                'discardNamed(uint256)', 'discardDividing(uint256)', 'discardEarly(uint256)',
                'discardUnassigned(uint256)', 'discardUnnamed(uint256)', 'voidWord(address,uint256)']),
    # Imports on legacy; rejected on via-IR (extcodesize before encoding) with either count.
    inline('void-call-storage-argument', '''interface ISink {
    function put(bytes calldata data) external;
}

contract C {
    bytes private stored;

    function run(address target) external {
        ISink(target).put(stored);
    }
}
''', ['run(address)']),
    inline('external-bytes-assignment', '''interface ISource {
    function get(uint256 n) external returns (bytes memory);
}

contract C {
    uint256 private total;

    function run(address source, uint256 n) external returns (bytes memory result) {
        result = ISource(source).get(n);
    }
}
''', ['run(address,uint256)'], expect='same-rejection'),
    fixture('fixture-narrow-event-sequence', 'Contracts/SolidityImportSmoke/NarrowEventSequence.sol',
            'SequenceFixture', ['change(uint128)', 'fail()', 'read()']),
    fixture('fixture-yul-narrow-result', 'Contracts/SolidityImportSmoke/YulNarrowResultOneSlot.sol',
            'YulNarrowResultOneSlot', [
                'pairWords(uint256,uint256)', 'pairRaw(uint256,uint256)', 'pairUse(uint256,uint256)',
                'mulSat(uint256,uint256)', 'mulTry(uint256,uint256)', 'readBackRaw(uint256)',
                'squareRaw(uint8)', 'localWord(uint256)', 'localUses(uint256)', 'localKey(uint256)',
                'clampedRaw(uint256,uint256)', 'queryPair(address)', 'sendFlag(address,uint256)',
                'transferChecked(address,address,uint256)', 'packedFlag(uint256)', 'emitFlag(uint256)',
                'encodedFlag(uint256)', 'arrayFlag(uint256)', 'sameFlag(uint256,uint256)']),
    # A stateful helper call as the right `+` operand beside a local or parameter, as a lone
    # helper argument and as a using-for receiver (the A/B/C fixture of the same shapes).
    fixture('fixture-stateful-call-operand', 'Contracts/SolidityImportSmoke/StatefulCallOperandSequence.sol',
            'SequenceFixture', ['change(uint256)', 'fail()', 'read()']),
    inline('stateful-call-lone-argument', '''library WordDoubling {
    function twice(uint256 v) internal pure returns (uint256) {
        return v * 2;
    }
}

contract C {
    using WordDoubling for uint256;

    uint256 private total;

    function bump(uint256 by) internal returns (uint256) {
        total = total + by;
        return total;
    }

    function readPlus(uint256 v) internal view returns (uint256) {
        return v * 1000 + total;
    }

    function argument(uint256 x) external returns (uint256) {
        total = x;
        return readPlus(bump(5));
    }

    function receiver(uint256 x) external returns (uint256) {
        total = x;
        return bump(5).twice();
    }

    function operands(uint256 x) external returns (uint256) {
        uint256 a = x;
        return a + bump(5);
    }
}
''', ['argument(uint256)', 'receiver(uint256)', 'operands(uint256)']),
    # A `constant` / `immutable` left operand beside a stateful (non-view) helper; the helper's
    # event makes the call observable. Each is the contract's only state variable.
    inline('stateful-call-constant-operand', '''contract C {
    uint256 private constant K = 3;
    event Bumped(uint256 by);

    function bump(uint256 by) internal returns (uint256) {
        emit Bumped(by);
        return by + 1;
    }

    function run(uint256 x) external returns (uint256) {
        return K + bump(x);
    }
}
''', ['run(uint256)']),
    # A file-level constant is indexed as a constant but not as a state variable.
    inline('stateful-call-file-constant-operand', '''uint256 constant FILE_OFFSET = 3;

contract C {
    uint256 private total;

    function bump(uint256 by) internal returns (uint256) {
        total = total + by;
        return total;
    }

    function run(uint256 x) external returns (uint256) {
        total = x;
        return FILE_OFFSET + bump(5);
    }
}
''', ['run(uint256)']),
    # A helper parameter bound to a transaction-context value (`block.timestamp`).
    inline('stateful-call-context-operand', '''contract C {
    uint256 private total;

    function bump(uint256 by) internal returns (uint256) {
        total = total + by;
        return total;
    }

    function later(uint256 p) internal returns (uint256) {
        return p + bump(1);
    }

    function run(uint256 x) external returns (uint256) {
        total = x;
        return later(block.timestamp);
    }
}
''', ['run(uint256)']),
    inline('stateful-call-immutable-operand', '''contract C {
    uint256 private immutable base;
    event Bumped(uint256 by);

    constructor(uint256 b) {
        base = b;
    }

    function bump(uint256 by) internal returns (uint256) {
        emit Bumped(by);
        return by + 1;
    }

    function run(uint256 x) external returns (uint256) {
        return base + bump(x);
    }
}
''', ['run(uint256)']),
    # `total + bump()`: legacy reads `total` after the call, via-IR before it.
    inline('stateful-call-state-operand', '''contract C {
    uint256 private total;

    function bump(uint256 by) internal returns (uint256) {
        total = total + by;
        return total;
    }

    function run(uint256 x) external returns (uint256) {
        total = x;
        return total + bump(5);
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    # Checked binary operations and conditionals in unordered `checkEncodingScalar` positions
    # (#2830): the A/B/C fixture, dedicated binary and conditional sweeps across every unordered
    # caller, and encoding-time validation sibling rejections.
    fixture('fixture-encoding-scalar-unordered',
            'Contracts/SolidityImportSmoke/EncodingScalarUnorderedSequence.sol',
            'SequenceFixture', ['change(uint256)', 'fail()', 'read()']),
    inline('encoding-scalar-binary-unordered', '''interface ITarget {
    function accept(uint256 a, uint256 b) external;
    function pair(uint256 a, uint256 b) external view returns (uint256, uint256);
}

contract C {
    struct Pair {
        uint8 a;
        uint256 b;
    }

    mapping(uint256 => mapping(uint256 => uint256)) private grid;

    event Logged(bytes tag, uint256 value);

    function _touch(uint256 k) internal returns (uint256) {
        grid[k][0] += 1;
        return grid[k][0];
    }

    function digest(address target, bytes calldata b, uint256 x) external returns (uint256, bytes memory) {
        bytes32 h1 = keccak256(abi.encode(x + 1, 10 / x));
        bytes32 h2 = keccak256(abi.encode(b, x + 2));
        bytes32 h3 = keccak256(abi.encodePacked(uint16(x + 3), bytes.concat(bytes32(x - 1))));
        bytes32 h4 = keccak256(abi.encodeWithSelector(bytes4(uint32(x + 4)), x + 5));
        bytes32 h5 = keccak256(abi.encodeWithSignature("accept(uint256,uint256)", x + 6, x - 1));
        bytes32 h6 = keccak256(abi.encodeCall(ITarget.accept, (x + 7, x - 1)));
        bytes32 h7 = keccak256(abi.encode(Pair(uint8(x % 200) + uint8(1), x + 8)));
        bytes32 h8 = keccak256(abi.encode(grid[x + 1][x - 1], _touch(x)));
        (uint256 p, uint256 q) = ITarget(target).pair(x + 9, x - 1);
        emit Logged(b, x + 10);
        return (uint256(h1 ^ h2 ^ h3 ^ h4 ^ h5 ^ h6 ^ h7 ^ h8) ^ p ^ q, b);
    }
}
''', ['digest(address,bytes,uint256)']),
    inline('encoding-scalar-conditional-unordered', '''interface ITarget {
    function accept(uint256 a, uint256 b) external;
    function pair(uint256 a, uint256 b) external view returns (uint256, uint256);
}

contract C {
    struct Pair {
        uint8 a;
        uint256 b;
    }

    mapping(uint256 => mapping(uint256 => uint256)) private grid;

    event Logged(bytes tag, uint256 value);

    function _touch(uint256 k) internal returns (uint256) {
        grid[k][0] += 1;
        return grid[k][0];
    }

    function digest(address target, bytes calldata b, bool c, uint256 x) external returns (uint256, bytes memory) {
        bytes32 h1 = keccak256(abi.encode(c ? x : uint256(1), c ? uint256(2) : x));
        bytes32 h2 = keccak256(abi.encode(b, c ? x : uint256(3)));
        bytes32 h3 = keccak256(abi.encodePacked(c ? uint16(x) : uint16(4), bytes.concat(c ? bytes4(0x11223344) : bytes4(0x55667788))));
        bytes32 h4 = keccak256(abi.encodeWithSelector(c ? bytes4(0x12345678) : bytes4(0x87654321), c ? x : uint256(5)));
        bytes32 h5 = keccak256(abi.encodeWithSignature("accept(uint256,uint256)", c ? x : uint256(6), uint256(7)));
        bytes32 h6 = keccak256(abi.encodeCall(ITarget.accept, (c ? x : uint256(8), uint256(9))));
        bytes32 h7 = keccak256(abi.encode(Pair(c ? uint8(1) : uint8(2), c ? x : uint256(10))));
        bytes32 h8 = keccak256(abi.encode(grid[c ? x : 1][c ? 2 : x], _touch(x)));
        (uint256 p, uint256 q) = ITarget(target).pair(c ? x : uint256(11), uint256(12));
        emit Logged(b, c ? x : uint256(13));
        return (uint256(h1 ^ h2 ^ h3 ^ h4 ^ h5 ^ h6 ^ h7 ^ h8) ^ p ^ q, b);
    }
}
''', ['digest(address,bytes,bool,uint256)']),
    inline('encoding-calldata-static-struct-before-panic', '''contract C {
    struct Pair {
        uint8 a;
        uint256 b;
    }

    uint256 private total;

    function run(Pair calldata p, uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(p, 10 / x + total));
    }
}
''', ['run(Pair,uint256)'], expect='same-rejection'),
    inline('encoding-storage-enum-before-panic', '''contract C {
    enum Mode {
        A,
        B
    }

    struct EnumPair {
        Mode m;
        uint256 b;
    }

    EnumPair private s;

    function run(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(s.m, 10 / x));
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    inline('encoding-storage-signature-before-panic', '''contract C {
    string private sig;

    function run(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sig, 10 / x));
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    inline('encoding-scalar-zero-to-one', '''interface ITarget {
    function accept(uint256 a, uint256 b) external;
}

contract C {
    struct Pair {
        uint8 a;
        uint256 b;
    }

    event Logged(bytes tag, uint256 value);

    function digest(bytes calldata b, bool c, uint256 x) external returns (uint256, bytes memory) {
        bytes32 h1 = keccak256(abi.encode(x + 1, c ? x : 10 / x));
        bytes32 h2 = keccak256(abi.encode(b, c ? x + 2 : uint256(3)));
        bytes32 h3 = keccak256(abi.encodePacked(uint16(x + 3), bytes.concat(c ? bytes4(0x11223344) : bytes4(uint32(x - 1)))));
        bytes32 h4 = keccak256(abi.encodeWithSelector(c ? bytes4(0x12345678) : bytes4(uint32(x + 4)), x + 5));
        bytes32 h5 = keccak256(abi.encodeWithSignature("accept(uint256,uint256)", x + 6, c ? uint256(7) : x - 1));
        bytes32 h6 = keccak256(abi.encodeCall(ITarget.accept, (x + 7, c ? x - 1 : uint256(9))));
        bytes32 h7 = keccak256(abi.encode(Pair(uint8(x % 200) + uint8(1), c ? x : uint256(10))));
        emit Logged(b, c ? x + 10 : uint256(13));
        return (uint256(h1 ^ h2 ^ h3 ^ h4 ^ h5 ^ h6 ^ h7), b);
    }
}
''', ['digest(bytes,bool,uint256)'], base_count=0),
    inline('encoding-enum-struct-before-calldata-member', '''contract C {
    enum Mode {
        A,
        B
    }

    struct NarrowPair {
        uint8 a;
        uint256 b;
    }

    struct EnumPair {
        Mode m;
        uint256 b;
    }

    EnumPair private s;

    function run(NarrowPair calldata p) external view returns (bytes32) {
        return keccak256(abi.encode(s, p.a == 0 ? 1 : 2));
    }
}
''', ['run(NarrowPair)'], expect='same-rejection'),
    inline('encoding-storage-signature-before-calldata-struct', '''contract C {
    struct NarrowPair {
        uint8 a;
        uint256 b;
    }

    string private sig;

    function run(NarrowPair calldata p) external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sig, p));
    }
}
''', ['run(NarrowPair)'], expect='same-rejection'),
    inline('encoding-storage-string-beside-enum-struct', '''contract C {
    enum Mode {
        A,
        B
    }

    struct EnumPair {
        Mode m;
        uint256 b;
    }

    string private sig;
    EnumPair private s;

    function run(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(sig, s, x == 0 ? 1 : 2));
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    inline('encoding-storage-array-before-panic', '''contract C {
    uint256[] private arr;

    function run(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(arr, 10 / x));
    }
}
''', ['run(uint256)'], expect='same-rejection'),
    inline('encoding-storage-string-before-storage-conditional', '''contract C {
    mapping(uint256 => string) private sigs;

    function run(bool c, uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(sigs[0], c ? sigs[1] : sigs[2], x == 0 ? 1 : 2));
    }
}
''', ['run(bool,uint256)'], expect='same-rejection'),
    inline('encoding-calldata-struct-before-memory-cond-storage', '''contract C {
    struct NarrowPair {
        uint8 a;
        uint256 b;
    }

    string private sig;

    function run(NarrowPair calldata p, bool c) external view returns (bytes32) {
        return keccak256(abi.encode(p, c ? sig : "lit"));
    }
}
''', ['run(NarrowPair,bool)'], expect='same-rejection'),
    inline('encoding-scalar-memory-read-before-memory-write', '''contract C {
    struct Elem {
        uint256 a;
    }

    uint256 private slot0;

    function _writeElem(Elem memory e, uint256 v) internal pure returns (uint256) {
        e.a = v;
        return v + 10;
    }

    function run(Elem[] memory xs, bool c) external view returns (bytes32) {
        Elem memory e = xs[0];
        return keccak256(abi.encode(e.a == 1, c ? _writeElem(e, slot0 + 9) : 0));
    }
}
''', ['run(«Elem[]»,bool)']),
    inline('encoding-memory-struct-before-memory-write', '''contract C {
    struct Elem {
        uint256 a;
    }

    uint256 private slot0;

    function _writeElem(Elem memory e, uint256 v) internal pure returns (uint256) {
        e.a = v;
        return v + 10;
    }

    function run(Elem[] memory xs, bool c) external view returns (bytes32) {
        Elem memory e = xs[0];
        return keccak256(abi.encode(e, c ? _writeElem(e, slot0 + 9) : 0));
    }
}
''', ['run(«Elem[]»,bool)'], expect='same-rejection'),
    inline('encoding-storage-enum-helper-before-panic', '''contract C {
    enum Mode {
        Alpha,
        Beta
    }

    struct Box {
        Mode m;
        uint256 b;
    }

    Box private box;

    function _readMode() internal view returns (Mode) {
        return box.m;
    }

    function run(bool c, uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(c ? _readMode() : Mode.Alpha, 10 / x));
    }
}
''', ['run(bool,uint256)'], expect='same-rejection'),
    inline('encoding-memory-signature-before-memory-write', '''contract C {
    uint256 private slot0;

    function _overwriteBytes(bytes memory b) internal view returns (uint256) {
        uint256 ok;
        assembly {
            mstore(0x00, "g(uint256)")
            ok := staticcall(gas(), 4, 0x00, 10, add(b, 0x20), mload(b))
        }
        return ok + slot0;
    }

    function run(bool c) external view returns (bytes4) {
        bytes memory b = abi.encodePacked("f(uint256)");
        return bytes4(abi.encodeWithSignature(string(b), c ? _overwriteBytes(b) : 0));
    }
}
''', ['run(bool)'], expect='same-rejection'),
]

# Importer behaviour on main that still depends on the state-variable count. Each entry
# names the discrepancy kind the harness must observe on every listed profile.
EXPECTED_DISCREPANCIES = {}

# Self-tests of the harness itself; see the module docstring.
CONTROLS = [
    inline('control-probe-first', '''contract C {
    uint256 private total;

    function bump(uint256 x) external returns (uint256) {
        total = total + x;
        return total;
    }
}
''', ['bump(uint256)'], probe_at='start', expect='unsound-layout'),
    inline('control-model-change', '''contract C {
    uint256 private total;

    function bump(uint256 x) external returns (uint256) {
        total = total + x + 1;
        return total;
    }
}
''', ['bump(uint256)'], variant_edit=('x + 1;', 'x + 2;'), expect='model'),
]


class CaseFailure(Exception):
    pass


def solc_layout(directory, entry, contract):
    """solc's AST and storage layout for `contract`, plus the file that defines it."""
    request = {
        'language': 'Solidity',
        'sources': {entry: {'urls': [entry]}},
        'settings': {'evmVersion': 'osaka', 'outputSelection': {'*': {'': ['ast'], '*': ['storageLayout']}}},
    }
    result = subprocess.run([str(SOLC), '--base-path', str(directory), '--allow-paths', str(directory),
                             '--standard-json'], input=json.dumps(request), text=True,
                            capture_output=True, timeout=180, cwd=directory)
    output = json.loads(result.stdout)
    errors = [e.get('formattedMessage', e['message']) for e in output.get('errors', [])
              if e['severity'] == 'error']
    if errors:
        raise CaseFailure('solc: ' + '\n'.join(errors))
    for source_name, contracts in output.get('contracts', {}).items():
        if contract in contracts:
            layout = contracts[contract]['storageLayout']
            break
    else:
        raise CaseFailure(f'contract {contract} not found')
    definition = None
    for source_name, source in output['sources'].items():
        for node in source['ast'].get('nodes', []):
            if node.get('nodeType') == 'ContractDefinition' and node.get('name') == contract:
                definition = (source_name, node)
    if definition is None:
        raise CaseFailure(f'contract definition {contract} not found')
    return layout, definition, sum(state_variables(source['ast']) for source in output['sources'].values())


def state_variables(node):
    """State variable declarations under `node`, as the importer counts them (constants and
    immutables included)."""
    if isinstance(node, list):
        return sum(state_variables(child) for child in node)
    if not isinstance(node, dict):
        return 0
    own = 1 if node.get('nodeType') == 'VariableDeclaration' and node.get('stateVariable') else 0
    return own + sum(state_variables(value) for value in node.values() if isinstance(value, (dict, list)))


def layout_entries(layout):
    types = layout.get('types') or {}
    return [(entry['label'], int(entry['slot']), entry['offset'],
             types.get(entry['type'], {}).get('label', entry['type']))
            for entry in layout.get('storage', [])]


def insert_probe(text, node, at):
    """Insert the probe into the contract whose AST node is `node` (byte offsets)."""
    data = text.encode()
    start, length, _ = (int(part) for part in node['src'].split(':'))
    probe = (f'\n    uint256 private {PROBE};\n'
             f'    function {PROBE_FUNCTION}() external {{ {PROBE} = 1; }}\n').encode()
    if at == 'start':
        position = data.index(b'{', start) + 1
    else:
        position = start + length - 1
        if data[position:position + 1] != b'}':
            raise CaseFailure('contract body does not end with }')
    return (data[:position] + probe + data[position:]).decode()


def check_layout(base, variant):
    """The variant's layout must be the base layout plus one fresh-slot probe at the end."""
    base_entries = layout_entries(base)
    variant_entries = layout_entries(variant)
    originals = [entry for entry in variant_entries if entry[0] != PROBE]
    probes = [entry for entry in variant_entries if entry[0] == PROBE]
    if originals != base_entries or len(probes) != 1:
        return 'original storage variables moved'
    types = base.get('types') or {}
    end = max((int(entry['slot']) + -(-(entry['offset'] + int(types[entry['type']]['numberOfBytes'])) // 32)
               for entry in base.get('storage', [])), default=0)
    if probes[0][1] < end or probes[0][2] != 0:
        return f'probe slot {probes[0][1]} overlaps the original layout (first free slot {end})'
    return None


def driver(directory, entry, contract, functions, profiles):
    blocks = []
    for profile in profiles:
        listed = ''.join(f'  function {f}\n' for f in functions)
        blocks.append(f'solidity_import {profile}Import from "{directory}" entry "{entry}"\n'
                      f'  using {PROFILES[profile]}\n  contract {contract}\n{listed}')
        blocks.append(f'#eval IO.println (let s := normalizedModel {profile}Import.model\n'
                      f'  "@@{profile}@@" ++ toString s.length ++ "@@" ++ s)\n')
    return ('import Compiler.SolidityImport.Import\nopen Compiler.CompilationModel\n\n'
            '/-- The model with the probe storage field removed (see the harness docstring). -/\n'
            'def normalizedModel (m : CompilationModel) : String :=\n'
            f'  (repr {{ m with fields := m.fields.filter (·.name != "{PROBE}") }}).pretty 1000000\n\n'
            + '\n'.join(blocks))


DIAGNOSTIC = re.compile(r'([A-Za-z0-9_./-]+\.sol:\d+:\d+: [^\n]*\[solidity-import:[^\]]+\][^\n]*)')


def import_side(directory, entry, contract, functions, profiles, timeout):
    lean = directory / 'Check.lean'
    lean.write_text(driver(directory.relative_to(ROOT), entry, contract, functions, profiles))
    result = subprocess.run(['lake', 'env', 'lean', str(lean)], cwd=ROOT, text=True,
                            capture_output=True, timeout=timeout)
    log = result.stdout + result.stderr
    (directory / 'check.log').write_text(log)
    models = {}
    for profile in profiles:
        marker = f'@@{profile}@@'
        line = next((l for l in log.splitlines() if l.startswith(marker)), None)
        if line is None:
            models[profile] = None
            continue
        length, _, model = line[len(marker):].partition('@@')
        if not length.isdigit() or int(length) != len(model):
            raise CaseFailure(f'{directory.name} {profile}: model output truncated '
                              f'({len(model)} of {length} characters on the marker line)')
        models[profile] = model
    diagnostics = sorted(set(DIAGNOSTIC.findall(log)))
    return models, diagnostics, log


def run_case(case, output, timeout):
    base_dir = output / case['name'] / 'base'
    variant_dir = output / case['name'] / 'variant'
    for side in (base_dir, variant_dir):
        if 'directory' in case:
            shutil.copytree(ROOT / case['directory'], side, ignore=solidity_only)
        else:
            side.mkdir(parents=True)
            for name, text in case['files'].items():
                (side / name).write_text(text)
    base_layout, (source_name, node), base_count = solc_layout(base_dir, case['entry'], case['contract'])
    expected_base_count = case.get('base_count', 1)
    if 'expect' not in case and base_count != expected_base_count:
        raise CaseFailure(f'base declares {base_count} state variables; expected {expected_base_count} '
                          f'so the probe moves the count from {expected_base_count} to {expected_base_count + 1}')
    target = variant_dir / source_name
    text = insert_probe(target.read_text(), node, case.get('probe_at', 'end'))
    if 'variant_edit' in case:
        old, new = case['variant_edit']
        if text.count(old) != 1:
            raise CaseFailure(f'variant edit anchor {old!r} is not unique')
        text = text.replace(old, new)
    target.write_text(text)
    variant_layout, _, _ = solc_layout(variant_dir, case['entry'], case['contract'])
    unsound = check_layout(base_layout, variant_layout)
    if unsound:
        return {'kind': 'unsound-layout', 'detail': unsound}
    profiles = case.get('profiles', list(PROFILES))
    base = import_side(base_dir, case['entry'], case['contract'], case['functions'], profiles, timeout)
    variant = import_side(variant_dir, case['entry'], case['contract'], case['functions'], profiles, timeout)
    outcome = {}
    for profile in profiles:
        base_model, variant_model = base[0][profile], variant[0][profile]
        for side, (models, diagnostics, _) in (('base', base), ('variant', variant)):
            if models[profile] is None and not diagnostics:
                raise CaseFailure(f'{side} {profile}: no model and no [solidity-import] diagnostic; '
                                  f'see {side}/check.log')
        if base_model is None and variant_model is None:
            if base[1] != [d.replace(str(variant_dir), str(base_dir)) for d in variant[1]]:
                outcome[profile] = 'diagnostic'
            else:
                outcome[profile] = 'same-rejection'
        elif (base_model is None) != (variant_model is None):
            outcome[profile] = 'admission'
        elif base_model != variant_model:
            outcome[profile] = 'model'
        else:
            outcome[profile] = 'same'
    return {'kind': 'compared', 'profiles': outcome, 'baseDiagnostics': base[1],
            'variantDiagnostics': variant[1],
            'modelSha256': {p: hashlib.sha256((base[0][p] or '').encode()).hexdigest() for p in profiles}}


def judge(case, result):
    """None when the case behaved as required, else the reason it did not."""
    expect = case.get('expect') or EXPECTED_DISCREPANCIES.get(case['name'])
    if result['kind'] == 'unsound-layout':
        if expect == 'unsound-layout':
            return None
        return f"normalization unsound: {result['detail']}"
    if expect == 'unsound-layout':
        return 'layout check accepted a probe that shifts the original variables'
    observed = set(result['profiles'].values())
    if expect is None:
        bad = {p: o for p, o in result['profiles'].items() if o not in ('same', 'same-rejection')}
        if bad:
            return f'state-count discrepancy: {bad}; base {result["baseDiagnostics"]}; variant {result["variantDiagnostics"]}'
        if observed == {'same-rejection'}:
            return f'positive control rejected on every profile: {result["baseDiagnostics"]}'
        return None
    if observed != {expect}:
        return f'expected a {expect} discrepancy on every profile, observed {result["profiles"]}'
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('--only', help='run only cases whose name contains this text')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--timeout', type=int, default=900)
    args = parser.parse_args()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='state-count-invariance-', dir=ROOT / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    if not output.is_relative_to(ROOT):
        raise SystemExit('--output must be inside the package root (solidity_import resolves paths there)')
    results, failures = [], []
    for case in CASES + CONTROLS:
        if args.only and args.only not in case['name']:
            continue
        try:
            result = run_case(case, output, args.timeout)
        except (CaseFailure, subprocess.TimeoutExpired, OSError) as error:
            result = {'kind': 'error', 'detail': str(error)}
        reason = (f"harness error: {result['detail']}" if result['kind'] == 'error'
                  else judge(case, result))
        results.append({'case': case['name'], 'result': result, 'failure': reason})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        if reason:
            failures.append(f"{case['name']}: {reason}")
            print(f"FAIL state-count-invariance-{case['name']}: {reason}", flush=True)
        else:
            print(f"pass state-count-invariance-{case['name']}", flush=True)
    if failures:
        raise SystemExit('state-count invariance failed:\n' + '\n'.join(failures) + f'\nartifacts: {output}')
    print(f'state-count invariance passed: {output}')


if __name__ == '__main__':
    main()
