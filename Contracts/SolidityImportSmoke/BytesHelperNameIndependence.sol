// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A two-parameter `bytes memory` helper is modeled by its own body, whatever its name. The
// helper name `callHook` once selected a fixed low-level CALL lowering in place of the body.

// The same body under two names: both must import, and agree with solc.
contract BytesHelperNameIndependence {
    uint256 private first = 7;
    uint256 private second = 9;

    function callHook(address self, bytes memory data) internal pure returns (bytes memory) {
        return abi.encodePacked(data, self);
    }

    function wrapBytes(address self, bytes memory data) internal pure returns (bytes memory) {
        return abi.encodePacked(data, self);
    }

    function viaHookName(uint256 x) external pure returns (bytes memory) {
        return callHook(address(uint160(x)), abi.encode(x));
    }

    function viaOtherName(uint256 x) external pure returns (bytes memory) {
        return wrapBytes(address(uint160(x)), abi.encode(x));
    }
}

// A helper that performs a low-level CALL and copies the return data into a fresh array
// from the free-memory pointer. It is lowered through its body like any other helper.
contract LowLevelCallBytesHelper {
    error HookCallFailed();
    error InvalidHookResponse();

    uint256 private first = 7;
    uint256 private second = 9;

    function callHook(address self, bytes memory data) internal returns (bytes memory result) {
        bool success;
        assembly ("memory-safe") {
            success := call(gas(), self, 0, add(data, 0x20), mload(data), 0, 0)
        }
        if (!success) revert HookCallFailed();
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(0x40, add(result, and(add(returndatasize(), 0x3f), not(0x1f))))
            mstore(result, returndatasize())
            returndatacopy(add(result, 0x20), 0, returndatasize())
        }
        if (result.length < 32 || bytes4(result) != bytes4(data)) revert InvalidHookResponse();
    }

    function ping(address target) external returns (bytes memory) {
        first += 1;
        return callHook(target, abi.encodePacked(bytes4(0x12345678), second));
    }
}
