// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

/// Memory structs with `bytes` and `enum` members: positional and named constructors,
/// uninitialized struct locals, pointer aliasing vs `delete s` vs `delete s.payload`,
/// bidirectional `bytes memory` buffer sharing vs calldata/storage copying, byte-lane
/// reads/writes/deletes, single/named/multi-return helpers, root `memory`/`calldata`
/// parameters and named/unnamed returns, `abi.encode*`, and `abi.decode` from both
/// `bytes memory` and `bytes calldata` across 0-, 31-, 32-, 33-, and 70-byte payloads.
contract SequenceFixture {
    enum Kind {
        None,
        Exact,
        Prefix,
        Custom
    }

    enum Mode {
        Pass,
        Strict,
        Mask
    }

    struct Clause {
        uint8 parent;
        Kind kind;
        Mode mode;
        bytes payload;
        bool invert;
    }

    uint8 internal lastParent;
    uint8 internal lastKind;
    uint8 internal lastMode;
    bool internal lastInvert;
    bytes internal storedPayload;
    bytes32 internal lastDigest;
    uint256 internal stepCount;

    function externalSink(Clause calldata c, uint256 salt) external pure {
        c;
        salt;
    }

    function _fillBytes(uint256 len, uint8 seed) internal pure returns (bytes memory) {
        unchecked {
            bytes memory buf = new bytes(len);
            uint256 cap = len < 4 ? len : 4;
            for (uint256 i = 0; i < cap; ++i) {
                buf[i] = bytes1(uint8((seed + i * 13 + 7) & 0xff));
            }
            if (len > 31) {
                buf[31] = bytes1(uint8((seed + 0x31) & 0xff));
            }
            if (len > 32) {
                buf[32] = bytes1(uint8((seed + 0x52) & 0xff));
            }
            if (len > 0) {
                buf[len - 1] = bytes1(uint8((seed + len * 11 + 3) & 0xff));
            }
            return buf;
        }
    }

    function _makeClause(uint8 parent, Kind kind, Mode mode, bytes memory payload, bool invert)
        internal
        pure
        returns (Clause memory)
    {
        return Clause(parent, kind, mode, payload, invert);
    }

    function _namedClause(bool populate, bool earlyExit, uint8 parent, Kind kind, Mode mode, bytes memory payload, bool invert)
        internal
        pure
        returns (Clause memory out)
    {
        if (!populate && earlyExit) {
            return out;
        }
        if (populate) {
            out = Clause({parent: parent, kind: kind, mode: mode, payload: payload, invert: invert});
        }
    }

    function _mutateOrRebind(Clause memory p, uint8 delta, bool rebind, bool wipe) internal pure returns (uint256) {
        p.parent = uint8((uint256(p.parent) + delta) & 0xff);
        if (p.payload.length > 0) {
            p.payload[0] = bytes1(uint8(delta ^ 0x5a));
        }
        if (rebind) {
            p = Clause(99, Kind.Custom, Mode.Mask, hex"deadbeef", true);
        } else if (wipe) {
            delete p;
        }
        return uint256(p.parent) + p.payload.length;
    }

    function _unpackClause(bytes memory raw, uint256 cursor)
        private
        pure
        returns (Clause memory, uint256)
    {
        Clause memory decoded = abi.decode(raw, (Clause));
        return (decoded, cursor + decoded.payload.length + 32);
    }

    function _loadAndTweak(bytes memory raw, uint256 cursor, bool tweak)
        internal
        pure
        returns (Clause memory item, uint256 nextCursor)
    {
        if (!tweak) {
            return _unpackClause(raw, cursor);
        }
        (item, nextCursor) = _unpackClause(raw, cursor);
        item.mode = Mode.Strict;
        if (item.payload.length > 1) {
            item.payload[item.payload.length - 1] = bytes1(0x7f);
        }
        nextCursor += 1;
    }

    function _digestClause(Clause memory c, uint256 tag) internal pure returns (bytes32) {
        bytes32 headWord = bytes32(c.payload);
        uint256 which = tag % 3;
        if (which == 0) {
            return keccak256(abi.encode(c, tag)) ^ headWord;
        } else if (which == 1) {
            return keccak256(abi.encodeWithSelector(SequenceFixture.externalSink.selector, c, tag)) ^ headWord;
        } else {
            return keccak256(abi.encodeCall(SequenceFixture.externalSink, (c, tag))) ^ headWord;
        }
    }

    function _pickLength(uint256 sel) internal pure returns (uint256) {
        uint256 m = sel % 5;
        if (m == 0) return 0;
        if (m == 1) return 31;
        if (m == 2) return 32;
        if (m == 3) return 33;
        return 70;
    }

    function _record(Clause memory c, bytes32 extra) internal {
        lastParent = c.parent;
        lastKind = uint8(c.kind);
        lastMode = uint8(c.mode);
        lastInvert = c.invert;
        storedPayload = c.payload;
        lastDigest = _digestClause(c, stepCount) ^ extra;
        stepCount += 1;
    }

    function change(uint256 x) external returns (Clause memory) {
        uint256 shape = x % 8;
        uint256 y = x / 8;
        Clause memory result;
        bytes32 extra;
        if (shape == 0) {
            // 0-, 31-, 32-, 33-, and 70-byte payloads + enum conversions (Panic(0x21) out of range).
            Kind k = Kind(y & 7);
            Mode m = Mode((y >> 3) & 3);
            uint256 len = _pickLength(y >> 5);
            bool populate = ((y >> 8) & 1) == 0;
            bytes memory buf = _fillBytes(len, uint8((y >> 9) & 0xff));
            Clause memory base = _makeClause(uint8((y >> 17) & 0xff), k, m, buf, ((y >> 25) & 1) != 0);
            result = _namedClause(populate, ((y >> 26) & 1) != 0, base.parent, base.kind, base.mode, base.payload, base.invert);
            extra = bytes32(result.payload);
            if (result.payload.length > 0) {
                extra = extra ^ bytes32(result.payload[result.payload.length - 1]);
            }
        } else if (shape == 1) {
            // Struct pointer aliasing (`aliasRef = primary`), helper `S memory` param mutation vs rebind,
            // `delete primary.payload` (shared) vs `delete primary` (allocates fresh zeroed struct).
            uint256 len = _pickLength(y);
            bytes memory buf = _fillBytes(len, uint8(y >> 4));
            Clause memory primary = Clause(uint8(y & 0x3f), Kind.Exact, Mode.Pass, buf, (y & 1) == 0);
            Clause memory aliasRef = primary;
            primary.parent += 3;
            uint256 helperOut = _mutateOrRebind(
                primary,
                uint8(((y >> 6) & 0x1f) + 1),
                ((y >> 11) & 1) != 0,
                ((y >> 12) & 1) != 0
            );
            if (((y >> 13) & 1) != 0) {
                delete primary.payload;
            }
            if (((y >> 14) & 1) != 0) {
                delete primary;
            }
            result = ((y >> 15) & 1) == 0 ? aliasRef : primary;
            extra = bytes32(uint256(primary.parent) + (uint256(aliasRef.parent) << 16) + (primary.payload.length << 32) + (aliasRef.payload.length << 64) + (helperOut << 96)) ^ bytes32(aliasRef.payload);
        } else if (shape == 2) {
            // Bidirectional aliasing between `bytes memory buf`, `c.payload`, and `bytes memory payloadAlias = c.payload`,
            // contrasted with independent copy from storage `storedPayload`.
            uint256 len = _pickLength(y) == 0 ? 33 : _pickLength(y);
            bytes memory buf = new bytes(len + 0);
            uint256 cap = len < 4 ? len : 4;
            for (uint256 i = 0; i < cap; ++i) {
                buf[i] = bytes1(uint8((y + i * 7 + 3) & 0xff));
            }
            if (len > 31) {
                buf[31] = bytes1(uint8((y + 0x31) & 0xff));
            }
            if (len > 32) {
                buf[32] = bytes1(uint8((y + 0x52) & 0xff));
            }
            result = Clause({
                parent: uint8((y >> 8) & 0x7f),
                kind: Kind.Prefix,
                mode: Mode.Mask,
                payload: buf,
                invert: ((y >> 15) & 1) != 0
            });
            buf[0] = bytes1(uint8(0xa0 | (y & 0x0f)));
            result.payload[len - 1] = bytes1(uint8(0x50 | ((y >> 4) & 0x0f)));
            bytes memory payloadAlias = result.payload;
            if (len > 2 && ((y >> 16) & 1) != 0) {
                delete result.payload[len / 2];
            }
            Clause memory fromStore = Clause(1, Kind.Exact, Mode.Pass, storedPayload, false);
            if (fromStore.payload.length > 0) {
                fromStore.payload[0] = hex"ff";
            }
            extra = bytes32(buf[0]) ^ bytes32(payloadAlias[len - 1]) ^ keccak256(storedPayload) ^ keccak256(fromStore.payload);
        } else if (shape == 3) {
            // Multi-return helper `(Clause memory, uint256)` + tuple local + tuple reassignment.
            uint256 len = _pickLength(y);
            Clause memory seedClause = Clause(
                uint8(y & 0xff),
                Kind((y >> 8) % 4),
                Mode((y >> 10) % 3),
                _fillBytes(len, uint8((y >> 12) & 0xff)),
                ((y >> 20) & 1) != 0
            );
            bytes memory raw = abi.encode(seedClause);
            (Clause memory first, uint256 cur) = _loadAndTweak(raw, y & 0xff, ((y >> 21) & 1) != 0);
            if (((y >> 22) & 1) != 0) {
                (first, cur) = _loadAndTweak(abi.encode(first), cur, true);
            }
            result = first;
            extra = bytes32(cur);
        } else if (shape == 4) {
            // Uninitialized `Clause memory emptyLocal;`, conditional selection, and byte index bounds (`Panic(0x32)`).
            Clause memory emptyLocal;
            uint256 len = _pickLength(y);
            Clause memory built = Clause(7, Kind.Custom, Mode.Strict, _fillBytes(len, 0x33), true);
            result = (y & 1) == 0 ? emptyLocal : built;
            uint256 probeIdx = (y >> 4) & 0x7f;
            bytes32 lane = bytes32(0);
            if (((y >> 1) & 1) != 0) {
                lane = bytes32(result.payload[probeIdx]);
            }
            extra = lane ^ bytes32(emptyLocal.payload.length) ^ bytes32(emptyLocal.payload);
        } else if (shape == 5) {
            // Raw `abi.decode(bytes memory, (Clause))`: valid lengths and malformed words/offsets/lengths.
            uint256 variant = y % 7;
            uint256 p = variant == 3 ? 256 : 1;
            uint256 kOrd = variant == 1 ? 4 : 1;
            uint256 mOrd = variant == 2 ? 3 : 1;
            uint256 inv = variant == 4 ? 2 : 1;
            uint256 lenWord = variant == 5 ? (uint256(1) << 64) : (variant == 6 ? 33 : 0);
            bytes memory raw = variant == 0
                ? abi.encode(Clause(12, Kind.Prefix, Mode.Mask, _fillBytes(_pickLength(y >> 3), 0x41), true))
                : abi.encode(uint256(32), p, kOrd, mOrd, uint256(160), inv, lenWord, bytes32(uint256(0x99)));
            result = abi.decode(raw, (Clause));
            extra = keccak256(raw);
        } else if (shape == 6) {
            // Named helper fallthrough vs early `return out;` + reassignment of `s.payload` from concat / `new bytes`.
            result = _namedClause((y & 1) == 0, ((y >> 13) & 1) != 0, uint8((y >> 1) & 0xff), Kind.Exact, Mode.Strict, hex"010203", false);
            if (((y >> 9) & 1) != 0) {
                result.payload = bytes.concat(result.payload, _fillBytes(_pickLength(y >> 10), 0x21));
            } else if (((y >> 14) & 1) != 0) {
                uint256 freshLen = _pickLength(y >> 15);
                result.payload = new bytes(freshLen);
            }
            extra = bytes32(result.payload);
        } else {
            // `abi.encodeWithSignature` alongside `Clause` roundtrip.
            uint256 len = y % 4;
            result = Clause(uint8(stepCount), Kind((y >> 3) % 4), Mode((y >> 5) % 3), _fillBytes(len, 0x77), (y & 1) != 0);
            bytes memory sigEncoded = abi.encodeWithSignature("s((uint8,uint8,uint8,bytes,bool))", result);
            extra = keccak256(sigEncoded);
        }
        _record(result, extra);
        return result;
    }

    function inspectCalldata(Clause calldata c, uint256 idx) external pure returns (Clause memory) {
        if (idx == 999) {
            return c;
        }
        Clause memory copy = c;
        copy.parent = uint8((uint256(copy.parent) + 1) & 0xff);
        if (copy.payload.length > 0) {
            copy.payload[idx % copy.payload.length] = bytes1(0xee);
        }
        bytes32 origHash = keccak256(c.payload) ^ bytes32(c.payload);
        if (origHash == bytes32(0)) {
            copy.invert = !copy.invert;
        }
        return copy;
    }

    function inspectMemory(Clause memory c, bytes memory extra) external pure returns (Clause memory out) {
        out = c;
        c.parent = uint8((uint256(c.parent) + 2) & 0xff);
        if (extra.length > 0) {
            out.payload = extra;
        }
    }

    function decodeCalldata(bytes calldata raw) external pure returns (Clause memory) {
        return abi.decode(raw, (Clause));
    }

    function fail() external pure {
        revert();
    }

    function read() external view returns (Clause memory out) {
        out.parent = lastParent;
        out.kind = Kind(lastKind);
        out.mode = Mode(lastMode);
        out.payload = storedPayload;
        out.invert = lastInvert;
        if (stepCount % 5 == 4) {
            delete out.payload;
        } else if (stepCount % 7 == 6) {
            delete out;
        }
    }
}
