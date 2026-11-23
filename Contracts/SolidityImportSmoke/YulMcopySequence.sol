// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `mcopy(dst, src, size)` (EIP-5656). A literal copy inside the scratch words below 0x40
// whose source bytes the same Yul block wrote on every path is modeled exactly, with memmove
// semantics when the ranges overlap; a zero size copies nothing and expands no memory,
// whatever its offsets. Each arm reads the copy back through `mload` or `revert` data.
// Other shapes are rejected (YulMcopyChecks.lean).
contract SequenceFixture {
    uint256 private total;

    function change(uint256 x) external returns (uint256) {
        uint256 y;
        if (x % 8 == 0) {
            // One whole scratch word into the other.
            assembly ("memory-safe") {
                mstore(0x00, x)
                mcopy(0x20, 0x00, 0x20)
                y := mload(0x20)
            }
        }
        if (x % 8 == 1) {
            // The destination starts after the source and overlaps it.
            assembly ("memory-safe") {
                mstore(0x00, x)
                mstore(0x20, not(x))
                mcopy(0x05, 0x00, 0x30)
                revert(0x00, 0x40)
            }
        }
        if (x % 8 == 2) {
            // The destination starts before the source and overlaps it.
            assembly ("memory-safe") {
                mstore(0x00, not(x))
                mstore(0x20, x)
                mcopy(0x00, 0x07, 0x39)
                revert(0x00, 0x40)
            }
        }
        if (x % 8 == 3) {
            // A zero size: offsets far past memory, nothing copied.
            assembly ("memory-safe") {
                mstore(0x00, x)
                mcopy(not(x), x, 0)
                y := mload(0x00)
            }
        }
        if (x % 8 == 4) {
            // Single bytes at both ends of the scratch words.
            assembly ("memory-safe") {
                mstore(0x00, x)
                mstore(0x20, shl(8, x))
                mcopy(0x3f, 0x00, 0x01)
                mcopy(0x00, 0x3e, 0x01)
                revert(0x00, 0x40)
            }
        }
        if (x % 8 == 5) {
            // The whole scratch space onto itself, then a copy straddling both words.
            assembly ("memory-safe") {
                mstore(0x00, x)
                mstore(0x20, mul(x, 3))
                mcopy(0x00, 0x00, 0x40)
                mcopy(0x10, 0x18, 0x20)
                y := xor(mload(0x00), mload(0x20))
            }
        }
        total = total + y % 1000;
        return total;
    }

    // The stateful harness's reverting call: its write is rolled back.
    function fail() external {
        total = total + 1;
        revert();
    }

    function read() external view returns (uint256) {
        return total;
    }
}
