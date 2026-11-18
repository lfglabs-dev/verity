// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `revert(offset, size)` with a nonzero size returns `size` memory bytes as revert data.
// There is no lowering for that, so the importer rejects it with a located error. It used to
// import as a revert with no data when the sources declared more than one state variable.
contract YulRevertData {
    uint256 private a;
    uint256 private b;
    function selectorRevert(uint256 x) external {
        a = x;
        if (x == 0) {
            assembly ("memory-safe") {
                mstore(0, 0x8baa579f00000000000000000000000000000000000000000000000000000000)
                revert(0, 4)
            }
        }
        b = x;
    }
    function sizedRevert(uint256 n) external pure {
        assembly ("memory-safe") {
            revert(0, n)
        }
    }
}
