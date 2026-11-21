// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `mcopy` shapes outside the modeled scratch-space slice (YulMcopyChecks.lean).
contract YulMcopy {
    function unwrittenSource(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mcopy(0x20, 0x00, 0x20)
            y := add(x, 1)
        }
    }
    function sizedCopy(uint256 n) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, n)
            mcopy(0x20, 0x00, n)
            y := n
        }
    }
    function freePointerDestination(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, x)
            mcopy(0x30, 0x00, 0x20)
            y := x
        }
    }
    function freePointerSource(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, x)
            mcopy(0x00, 0x20, 0x40)
            y := mload(0x00)
        }
    }
    function partlyWrittenSource(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, x)
            mcopy(0x00, 0x10, 0x20)
            y := mload(0x00)
        }
    }
    function bufferCopy(bytes memory target, bytes memory source) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mcopy(add(target, 0x20), add(source, 0x20), mload(source))
        }
        y = target.length;
    }
}
