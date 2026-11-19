// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `revert(offset, size)` reverts with `size` memory bytes. A literal range of scratch bytes
// (below 0x40) that the same Yul block wrote on every path is modeled exactly
// (`Stmt.revertMemory`): a left-aligned selector, a right-aligned selector, a selector with one
// word argument (right-aligned and shifted forms), two full words and the second word alone.
// Other ranges are rejected (YulRevertDataChecks.lean).
contract SequenceFixture {
    uint256 private total;
    function change(uint256 x) external returns (uint256) {
        if (x % 8 == 0) {
            assembly ("memory-safe") {
                mstore(0, 0x8baa579f00000000000000000000000000000000000000000000000000000000)
                revert(0, 4)
            }
        }
        if (x % 8 == 1) {
            assembly ("memory-safe") {
                mstore(0x00, 0x82b42900)
                revert(0x1c, 0x04)
            }
        }
        if (x % 8 == 2) {
            assembly ("memory-safe") {
                mstore(0x00, 0xa0a1a2a3)
                mstore(0x20, x)
                revert(0x1c, 0x24)
            }
        }
        if (x % 8 == 3) {
            assembly ("memory-safe") {
                mstore(0x00, x)
                mstore(0x20, add(x, 1))
                revert(0, 0x40)
            }
        }
        if (x % 8 == 4) {
            assembly ("memory-safe") {
                mstore(0x20, mul(x, 3))
                revert(0x20, 0x20)
            }
        }
        if (x % 8 == 5) {
            assembly ("memory-safe") {
                mstore(0x00, shl(224, 0xb1b2b3b4))
                mstore(0x04, x)
                revert(0x00, 0x24)
            }
        }
        total = total + x % 1000;
        return total;
    }
    function fail() external pure {
        assembly ("memory-safe") {
            mstore(0x00, 0xdeadbeef)
            revert(0x1c, 0x04)
        }
    }
    function read() external view returns (uint256) {
        return total;
    }
}
