// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

/// Memory/flat static structs with `enum` members: positional and named constructors,
/// uninitialized struct locals, member reads/writes/deletes, single- and multi-return
/// helpers (including forwarded multi-return tuples), root flat and nested-static struct
/// returns, `abi.decode` empty reverts, `E(x)` out-of-range `Panic(0x21)` conversions,
/// and static struct ABI encoding (`abi.encode`, `abi.encodeWithSelector`, `abi.encodeCall`).
contract SequenceFixture {
    enum Kind {
        Alpha,
        Beta,
        Gamma
    }

    enum Stage {
        Idle,
        Queued,
        Active,
        Paused,
        Closed
    }

    struct Header {
        address peer;
        uint96 amount;
        Kind kind;
    }

    struct Rule {
        uint64 index;
        Kind kind;
        Stage stage;
    }

    struct Snapshot {
        Header header;
        Stage stage;
        bytes32 digest;
    }

    address internal lastPeer;
    uint96 internal lastAmount;
    uint64 internal lastIndex;
    uint8 internal lastKind;
    uint8 internal lastStage;
    bytes32 internal lastDigest;
    uint256 internal stepCount;

    function externalTarget(Header calldata h, Stage s) external pure {
        h;
        s;
    }

    function _makeHeader(address peer, uint96 amount, Kind kind) internal pure returns (Header memory) {
        return Header(peer, amount, kind);
    }

    function _namedRule(bool populate, uint64 idx, Kind kind, Stage stage)
        internal
        pure
        returns (Rule memory r)
    {
        if (!populate) {
            return r;
        }
        r = Rule({stage: stage, index: idx, kind: kind});
    }

    function _unpackRule(bytes memory raw, uint256 cursor)
        private
        pure
        returns (Rule memory, uint256)
    {
        Rule memory item = abi.decode(raw, (Rule));
        return (item, cursor + 96);
    }

    function _loadRule(bytes memory raw, uint256 cursor, bool promote)
        internal
        pure
        returns (Rule memory loaded, uint256 nextCursor)
    {
        if (!promote) {
            return _unpackRule(raw, cursor);
        }
        (Rule memory base, uint256 endCursor) = _unpackRule(raw, cursor);
        base.stage = Stage.Active;
        return (base, endCursor + 1);
    }

    function _combineDigest(Header memory hdr, Rule memory rule, uint256 tag)
        internal
        pure
        returns (bytes32)
    {
        bytes memory a = abi.encode(hdr, rule, tag);
        bytes memory b = abi.encodeWithSelector(SequenceFixture.externalTarget.selector, hdr, rule.kind);
        bytes memory c = abi.encodeCall(SequenceFixture.externalTarget, (hdr, rule.stage));
        return keccak256(bytes.concat(keccak256(a), keccak256(b), keccak256(c)));
    }

    function change(uint256 x) external returns (Rule memory) {
        uint256 shape = x % 6;
        uint256 y = x / 6;
        if (shape == 0) {
            // Integer-to-enum conversions: 3..7 on Kind and 5..7 on Stage trigger Panic(0x21).
            Kind k = Kind(y & 7);
            Stage s = Stage((y >> 3) & 7);
            bool populate = ((y >> 6) & 1) == 0;
            address peer = address(uint160((y >> 7) ^ 0xbeef));
            uint96 amount = uint96((y >> 16) & 0xffffffffffff);
            uint64 idx = uint64((y >> 24) & 0xffffffff);
            Header memory hdr = _makeHeader(peer, amount, k);
            Rule memory rule = _namedRule(populate, idx, hdr.kind, s);
            lastPeer = hdr.peer;
            lastAmount = hdr.amount;
            lastIndex = rule.index;
            lastKind = uint8(rule.kind);
            lastStage = uint8(rule.stage);
            lastDigest = _combineDigest(hdr, rule, stepCount);
            if (hdr.kind == Kind.Gamma) {
                stepCount += 2;
            } else {
                stepCount += 1;
            }
            return rule;
        } else if (shape == 1) {
            // abi.decode inside multi-return helpers: out-of-range ordinals or uint64 revert empty.
            uint256 idxWord = y & 0x1ffffffffffffffff;
            uint256 kindWord = (y >> 65) & 7;
            uint256 stageWord = (y >> 68) & 7;
            bool promote = ((y >> 71) & 1) != 0;
            bytes memory raw = abi.encode(idxWord, kindWord, stageWord);
            (Rule memory loaded, uint256 cursor) = _loadRule(raw, y & 0xff, promote);
            Header memory hdr = Header({kind: loaded.kind, peer: msg.sender, amount: uint96(cursor)});
            lastPeer = hdr.peer;
            lastAmount = hdr.amount;
            lastIndex = loaded.index;
            lastKind = uint8(loaded.kind);
            lastStage = uint8(loaded.stage);
            lastDigest = _combineDigest(hdr, loaded, cursor);
            stepCount += 1;
            return loaded;
        } else if (shape == 2) {
            // Uninitialized struct local, enum-typed member writes (no check), conditional copy, delete.
            Rule memory scratch;
            scratch.index = uint64(y & 0xffff);
            scratch.kind = (y & 1) == 0 ? Kind.Gamma : Kind.Beta;
            scratch.stage = Stage((y >> 4) % 5);
            Rule memory chosen = ((y >> 1) & 1) == 0
                ? Rule({index: scratch.index, kind: scratch.kind, stage: scratch.stage})
                : Rule({index: scratch.index + 1, kind: Kind.Alpha, stage: scratch.stage});
            if (((y >> 2) & 1) != 0) {
                delete chosen.kind;
            }
            if (((y >> 3) & 1) != 0) {
                delete chosen;
            }
            Header memory hdr = _makeHeader(msg.sender, uint96(chosen.index), chosen.kind);
            lastPeer = hdr.peer;
            lastAmount = hdr.amount;
            lastIndex = chosen.index;
            lastKind = uint8(chosen.kind);
            lastStage = uint8(chosen.stage);
            lastDigest = _combineDigest(hdr, chosen, y & 0xff);
            stepCount += 1;
            return chosen;
        } else if (shape == 3) {
            // Signed int256-to-enum cast: negative (-2, -1) and >= 3 (3, 4) trigger Panic(0x21).
            int256 signedOrd = int256(y % 7) - 2;
            Kind k = Kind(signedOrd);
            Stage s = Stage((y >> 3) % 5);
            Rule memory rule = Rule(uint64((y >> 8) & 0xffff), k, s);
            lastIndex = rule.index;
            lastKind = uint8(rule.kind);
            lastStage = uint8(rule.stage);
            lastDigest = keccak256(abi.encode(rule));
            stepCount += 1;
            return rule;
        } else if (shape == 4) {
            // Unmasked uint256 cast source (e.g. y == 256, 2^255): must Panic(0x21), not mask low byte.
            Kind k = Kind(y);
            Header memory hdr = Header(address(uint160(stepCount + 1)), 9, k);
            Rule memory rule = Rule(uint64(stepCount), hdr.kind, Stage.Queued);
            lastPeer = hdr.peer;
            lastAmount = hdr.amount;
            lastIndex = rule.index;
            lastKind = uint8(rule.kind);
            lastStage = uint8(rule.stage);
            lastDigest = _combineDigest(hdr, rule, y);
            stepCount += 1;
            return rule;
        } else {
            // Raw uint256 word in abi.decode (e.g. y == 3, 256, 2^255): reverts with empty data.
            bytes memory raw = abi.encode(uint256(11), y, uint256(2));
            (Rule memory loaded, uint256 cursor) = _loadRule(raw, 32, false);
            lastIndex = loaded.index;
            lastKind = uint8(loaded.kind);
            lastStage = uint8(loaded.stage);
            lastDigest = keccak256(abi.encode(loaded, cursor));
            stepCount += 1;
            return loaded;
        }
    }

    function fail() external pure {
        revert();
    }

    function read() external view returns (Snapshot memory snap) {
        snap.header = Header(lastPeer, lastAmount, Kind(lastKind));
        snap.stage = Stage(lastStage);
        snap.digest = lastDigest;
        if (stepCount % 5 == 4) {
            delete snap.header;
        } else if (stepCount % 7 == 6) {
            snap = Snapshot({
                stage: Stage(lastStage),
                header: Header({kind: Kind(lastKind), peer: lastPeer, amount: lastAmount}),
                digest: bytes32(stepCount)
            });
        }
    }
}
