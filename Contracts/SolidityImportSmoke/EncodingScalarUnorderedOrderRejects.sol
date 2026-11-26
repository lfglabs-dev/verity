// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

// Encoding-time validation hazards and positive controls for unordered `checkEncodingScalar`
// arguments (#2830).
contract EncodingScalarUnorderedOrderRejects {
    enum Mode {
        Alpha,
        Beta
    }

    struct NarrowPair {
        uint8 a;
        uint256 b;
    }

    struct FullPair {
        uint256 a;
        uint256 b;
    }

    struct EnumPair {
        Mode m;
        uint256 b;
    }

    EnumPair internal enumStored;
    string internal sigStored;

    // Positive controls: inert sibling, panic before calldata struct, or unguarded 256-bit struct.
    function calldataStructBeforeInert(NarrowPair calldata p, uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encode(p, x == 0 ? 1 : x));
    }

    function panicBeforeCalldataStruct(NarrowPair calldata p, uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encode(10 / x, p));
    }

    function unguardedCalldataStructBeforePanic(FullPair calldata p, uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encode(p, 10 / x));
    }

    function storageSignatureBeforeInert(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sigStored, x == 0 ? 1 : x));
    }

    // Located rejections: solc validates calldata narrow struct members, storage enum ordinals
    // and storage signature strings only while encoding, after every argument has run.
    function calldataStructBeforePanic(NarrowPair calldata p, uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encode(p, 10 / x));
    }

    function enumStorageStructBeforePanic(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(enumStored, 10 / x));
    }

    function enumStorageMemberInEncode(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(enumStored.m, 10 / x));
    }

    function storageSignatureBeforePanic(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sigStored, 10 / x));
    }

    function enumStorageStructBeforeCalldataMember(NarrowPair calldata p) external view returns (bytes32) {
        return keccak256(abi.encode(enumStored, p.a == 0 ? 1 : 2));
    }

    function storageSignatureBeforeCalldataMember(NarrowPair calldata p) external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sigStored, p.a == 0 ? 1 : 2));
    }

    function storageSignatureBeforeCalldataStruct(NarrowPair calldata p) external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sigStored, p));
    }

    function storageSignatureBeforeEnumStorageStruct() external view returns (bytes32) {
        return keccak256(abi.encodeWithSignature(sigStored, enumStored));
    }

    function storageStringBesideEnumStorageStruct(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(sigStored, enumStored, x == 0 ? 1 : 2));
    }

    function calldataArrayBeforeEnumStorageStruct(uint8[] calldata xs) external view returns (bytes32) {
        return keccak256(abi.encode(xs, enumStored));
    }

    function calldataStructBeforeCalldataMember(NarrowPair calldata p, NarrowPair calldata q) external pure returns (bytes32) {
        return keccak256(abi.encode(p, q.a == 0 ? 1 : q.a));
    }
}
