// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `revert(offset, size)` with a nonzero size returns `size` memory bytes as revert data. It is
// modeled only for a literal range below 0x40 that the same Yul block wrote on every path
// (YulRevertMemorySequence); every other shape is rejected
// with a location. It used to import as a revert with no data when the sources declared more
// than one state variable.
contract YulRevertData {
    uint256 private a;
    uint256 private b;
    function unwrittenRevert(uint256 x) external {
        a = x;
        if (x == 0) {
            assembly ("memory-safe") {
                revert(0, 4)
            }
        }
        b = x;
    }
    function sizedRevert(uint256 n) external pure {
        assembly ("memory-safe") {
            mstore(0, n)
            revert(0, n)
        }
    }
    function conditionalWriteRevert(uint256 x) external pure {
        assembly ("memory-safe") {
            if x {
                mstore(0, x)
            }
            revert(0, 4)
        }
    }
    function beyondScratchRevert(uint256 x) external pure {
        assembly ("memory-safe") {
            mstore(0, x)
            mstore(0x20, x)
            revert(0, 0x60)
        }
    }
    function freePointerRevert(uint256) external pure {
        assembly ("memory-safe") {
            let p := mload(0x40)
            mstore(0x40, p)
            revert(0x40, 0x20)
        }
    }
}
