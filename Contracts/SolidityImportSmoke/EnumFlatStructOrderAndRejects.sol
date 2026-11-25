// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

interface IStaticInspector {
    function inspect(EnumFlatStructOrderAndRejects.Pair calldata p) external view returns (uint256);
}

contract EnumFlatStructOrderAndRejects {
    enum Kind {
        Alpha,
        Beta,
        Gamma
    }

    struct Pair {
        uint256 ratio;
        Kind kind;
    }

    struct WithArray {
        Kind kind;
        bytes32[] items;
    }

    struct WithBytes {
        uint256 idx;
        Kind kind;
        bytes payload;
    }

    uint256 internal anchor;

    function namedOrder(uint256 denom, uint256 rawKind) external pure returns (uint256) {
        Pair memory p = Pair({kind: Kind(rawKind), ratio: 100 / denom});
        return p.ratio + uint256(p.kind);
    }

    function dirtyNarrowCast() external pure returns (uint256) {
        uint8 raw;
        assembly {
            raw := 257
        }
        Pair memory p = Pair(5, Kind(raw));
        return p.ratio + uint256(p.kind);
    }

    function staticCallStructArg(address target, Kind k) external view returns (uint256) {
        Pair memory p = Pair(anchor + 1, k);
        return IStaticInspector(target).inspect(p);
    }

    function asmReadStruct(uint256 x) external pure returns (uint256) {
        Pair memory p = Pair(x, Kind.Beta);
        uint256 w;
        assembly {
            w := mload(p)
        }
        return w;
    }

    function asmKeccakStruct(uint256 x) external pure returns (uint256) {
        Pair memory p = Pair(x, Kind.Beta);
        bytes32 h;
        assembly {
            h := keccak256(p, 64)
        }
        return uint256(h);
    }

    function asmDirtyEnumLocal() external pure returns (uint256) {
        Kind k;
        assembly {
            k := 5
        }
        Pair memory p = Pair(1, k);
        return uint256(p.kind);
    }

    function dynamicArrayMemberStruct(uint256 x) external pure returns (uint256) {
        WithArray memory w = WithArray(Kind.Alpha, new bytes32[](x));
        return uint256(w.kind);
    }

    function _loadWithBytes() internal pure returns (WithBytes memory, uint256) {
        return (WithBytes(0, Kind.Alpha, ""), 0);
    }

    function multiReturnBytesMember() external pure returns (uint256) {
        (, uint256 c) = _loadWithBytes();
        return c;
    }

    struct WithEnumArray {
        Kind kind;
        Kind[] modes;
    }

    function enumArrayMemberStruct(uint256 x) external pure returns (uint256) {
        WithEnumArray memory w = WithEnumArray(Kind.Alpha, new Kind[](x));
        return uint256(w.kind);
    }

    function uninitArrayMemberLocal() external pure returns (uint256) {
        WithArray memory w;
        w.kind = Kind.Beta;
        return uint256(w.kind);
    }
}

contract EnumStorageWriteRejects {
    enum Kind {
        Alpha,
        Beta
    }

    struct Pair {
        uint64 ratio;
        Kind kind;
    }

    struct Outer {
        Pair sub;
        uint256 tag;
    }

    Pair internal stored;
    Outer internal outer;

    function wholeStorageWrite(uint64 r, Kind k) external {
        stored = Pair(r, k);
    }

    function nestedStorageWrite(uint64 r, Kind k) external {
        outer.sub = Pair(r, k);
    }
}
