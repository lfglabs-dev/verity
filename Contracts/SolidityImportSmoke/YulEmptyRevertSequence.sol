// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `revert(offset, 0)` reverts with no data, whatever the offset, in a contract with one state
// variable. A nonzero size returns memory bytes and is rejected (YulRevertDataChecks.lean).
contract SequenceFixture {
    uint256 private total;
    function change(uint256 x) external returns (uint256) {
        if (x % 5 == 0) {
            assembly ("memory-safe") {
                revert(0, 0)
            }
        }
        if (x % 5 == 1) {
            assembly ("memory-safe") {
                revert(0x80, 0)
            }
        }
        total = total + x % 1000;
        return total;
    }
    function fail() external pure {
        assembly ("memory-safe") {
            revert(0x40, 0)
        }
    }
    function read() external view returns (uint256) {
        return total;
    }
}
