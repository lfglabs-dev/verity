// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Solidity low-level `<address>.staticcall(payload)` with `bytes memory` payloads. The
// ERC-1271 check (`isValidSignature`) is the motivating shape; the other roots observe the
// success flag, the complete return data and the payload bytes (through a calldata-folding
// responder) separately.
interface ISignatureValidator {
    function isValidSignature(bytes32 hash, bytes calldata signature)
        external view returns (bytes4);
    function probe(uint256 a, bytes32 b) external view returns (bytes32);
}

contract LowLevelStaticcallFixture {
    // `ISignatureValidator.isValidSignature.selector`.
    bytes4 internal constant MAGIC = 0x1626ba7e;

    bool private lastOk;
    uint256 private lastLength;
    bytes32 private lastWord;

    function isValid(address signer, bytes32 hash) external view returns (bool) {
        (bool success, bytes memory returnData) = signer.staticcall(
            abi.encodeWithSelector(ISignatureValidator.isValidSignature.selector, hash));
        return success && bytes4(returnData) == MAGIC;
    }

    // The selector as a `bytes4` constant and as a parameter, not a `.selector` expression.
    function isValidConstantSelector(address signer, bytes32 hash) external view returns (bool) {
        (bool success, bytes memory returnData) =
            signer.staticcall(abi.encodeWithSelector(MAGIC, hash));
        return success && bytes4(returnData) == MAGIC;
    }

    // ERC-1271 check with a dynamic `bytes calldata` signature (#2948 `checkBytes`).
    function checkBytes(address signer, bytes32 hash, bytes calldata signature)
        external view returns (bool)
    {
        (bool success, bytes memory returnData) =
            signer.staticcall(abi.encodeWithSelector(MAGIC, hash, signature));
        return success && bytes4(returnData) == MAGIC;
    }

    function withSelector(address target, bytes4 selector, uint256 a)
        external view returns (bool, bytes32)
    {
        bytes4 dirty;
        assembly { dirty := or(selector, shr(32, a)) }
        bytes memory onlySel = abi.encodeWithSelector(dirty);
        bytes32 rawWord;
        assembly { rawWord := mload(add(onlySel, 0x20)) }
        (bool ok, bytes memory ret) = target.staticcall(abi.encodeWithSelector(dirty, a));
        return (ok, keccak256(abi.encode(ret, rawWord)));
    }

    function observe(address target, uint256 a, bytes32 b)
        external view returns (bool, uint256, bytes32, bytes32)
    {
        (bool ok, bytes memory ret) =
            target.staticcall(abi.encodeWithSelector(ISignatureValidator.probe.selector, a, b));
        return (ok, ret.length, bytes32(ret), keccak256(ret));
    }

    // A `bytes memory` local payload without a selector.
    function fromLocal(address target, uint256 a) external view returns (bool, bytes32) {
        bytes memory payload = abi.encode(a, target);
        (bool ok, bytes memory ret) = target.staticcall(payload);
        return (ok, keccak256(ret));
    }

    // A packed payload whose length is not a multiple of 32.
    function packed(address target, uint256 a) external view returns (bool, uint256, bytes32) {
        (bool ok, bytes memory ret) = target.staticcall(abi.encodePacked(uint40(a), a));
        return (ok, ret.length, keccak256(ret));
    }

    function onlySuccess(address target, bytes32 hash) external view returns (bool) {
        (bool ok, ) = target.staticcall(
            abi.encodeWithSelector(ISignatureValidator.isValidSignature.selector, hash));
        return ok;
    }

    function onlyData(address target, bytes32 hash) external view returns (bytes32) {
        (, bytes memory ret) = target.staticcall(
            abi.encodeWithSelector(ISignatureValidator.isValidSignature.selector, hash));
        return bytes32(ret);
    }

    // The return data of one call as the payload of the next, and an allocation after both.
    function chained(address target, bytes32 hash) external view returns (bytes32) {
        (bool ok, bytes memory ret) = target.staticcall(
            abi.encodeWithSelector(ISignatureValidator.isValidSignature.selector, hash));
        (bool ok2, bytes memory ret2) = target.staticcall(ret);
        return keccak256(abi.encode(ok, ok2, keccak256(ret), ret2.length, keccak256(ret2)));
    }

    // Storage writes after the call: STATICCALL cannot re-enter with a write.
    function record(address target, bytes32 hash) external returns (bool) {
        (bool ok, bytes memory ret) = target.staticcall(
            abi.encodeWithSelector(ISignatureValidator.isValidSignature.selector, hash));
        lastOk = ok;
        lastLength = ret.length;
        lastWord = bytes32(ret);
        return ok;
    }

    function stored() external view returns (bool, uint256, bytes32) {
        return (lastOk, lastLength, lastWord);
    }
}
