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
    uint256[] internal arrStored; mapping(uint256 => string) internal sigMap;

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

    function storageArrayBeforeInert(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(arrStored, x == 0 ? 1 : x));
    }

    function storageArrayBeforePanic(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(arrStored, 10 / x));
    }

    function storageArrayBeforeCalldataMember(NarrowPair calldata p) external view returns (bytes32) {
        return keccak256(abi.encode(arrStored, p.a == 0 ? 1 : 2));
    }

    function storageStringBesideStorageArray(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(sigStored, arrStored, x == 0 ? 1 : 2));
    }

    function calldataArrayBeforeStorageArray(uint8[] calldata xs) external view returns (bytes32) {
        return keccak256(abi.encode(xs, arrStored));
    }

    function storageStringBeforeStorageConditionalEncode(bool c, uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(sigMap[0], c ? sigMap[1] : sigMap[2], x == 0 ? 1 : 2));
    }

    function storageStringBeforeStorageConditionalPacked(bool c, uint256 x) external view returns (bytes32) {
        return keccak256(abi.encodePacked(sigMap[0], c ? sigMap[1] : sigMap[2], x == 0 ? 1 : 2));
    }

    function enumStorageStructBeforeMemoryCondFromStorage(bool c) external view returns (bytes32) {
        return keccak256(abi.encode(enumStored, c ? sigStored : "lit"));
    }

    function calldataStructBeforeMemoryCondFromStorage(NarrowPair calldata p, bool c) external view returns (bytes32) {
        return keccak256(abi.encode(p, c ? sigStored : "lit"));
    }

    function storageArrayBeforeMemoryCondFromStorage(bool c) external view returns (bytes32) {
        return keccak256(abi.encode(arrStored, c ? sigStored : "lit"));
    }

    function storageConditionalBeforeMemoryCondFromStorage(bool c1, bool c2) external view returns (bytes32) {
        return keccak256(abi.encodePacked(c1 ? sigMap[0] : sigMap[1], c2 ? sigMap[2] : "lit"));
    }

    struct Elem {
        uint256 a;
    }

    struct DynElem {
        uint256 a;
        bytes b;
    }

    event IndexedAfterData(bytes tag, uint256 dataArg, uint256 indexed topicArg);

    function _writeElem(Elem memory e, uint256 v) internal pure returns (uint256) {
        e.a = v;
        return v + 10;
    }

    function _writeDynElem(DynElem memory d, uint256 v) internal pure returns (uint256) {
        d.a = v;
        return v + 10;
    }

    function _writeScalarArray(uint256[] memory xs, uint256 v) internal pure returns (uint256) {
        xs[0] = v;
        return v + 10;
    }

    function scalarReadBeforeMemoryWriteStatic(Elem[] memory xs) external pure returns (bytes32) {
        Elem memory e = xs[0];
        return keccak256(abi.encode(e.a == 1, _writeElem(e, 9)));
    }

    function scalarReadBeforeMemoryWriteDynamic(Elem[] memory xs) external pure returns (bytes32) {
        Elem memory e = xs[0];
        return keccak256(abi.encode("tag", e.a == 1, _writeElem(e, 9)));
    }

    function memoryStructBeforeMemoryWrite(Elem[] memory xs, bool c) external pure returns (bytes32) {
        Elem memory e = xs[0];
        return keccak256(abi.encode(e, c ? _writeElem(e, 9) : 0));
    }

    function memoryBytesBeforeMemoryWrite(DynElem memory d, bool c) external pure returns (bytes32) {
        return keccak256(abi.encode(d.b, c ? _writeDynElem(d, 9) : 0));
    }

    function memoryBytesPackedBeforeMemoryWrite(DynElem memory d, bool c) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(d.b, uint8(c ? _writeDynElem(d, 9) : 0)));
    }

    function memoryArrayBeforeMemoryWrite(bool c) external pure returns (bytes32) {
        uint256[] memory ys = new uint256[](1);
        return keccak256(abi.encode(ys, c ? _writeScalarArray(ys, 9) : 0));
    }

    function emitDataMemoryWriteBeforeTopic(bytes calldata tag, Elem[] memory xs, bool c) external {
        Elem memory e = xs[0];
        emit IndexedAfterData(tag, c ? _writeElem(e, 9) : 0, e.a);
    }
}
