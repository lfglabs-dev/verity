// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Custom errors with `bytesN` parameters (here the castable widths 1, 4, 12, 20): each
// argument is ABI-encoded as a left-aligned word and the selector hashes `bytesN`.
contract SequenceFixture {
    error LockedSelector(bytes4 selector);
    error Tagged(bytes1 tag, uint256 value, bytes12 prefix);
    error Wide(bytes20 head, bytes4 tail);

    uint256 private saved;

    function change(uint256 next) external returns (uint256) {
        saved = next;
        bytes4 selector = bytes4(bytes32(next));
        if (next % 4 == 1) {
            revert LockedSelector(selector);
        }
        bytes1 tag = bytes1(bytes32(next << 248));
        bytes12 prefix = bytes12(bytes32(next << 8));
        if (next % 4 == 2) {
            revert Tagged(tag, next, prefix);
        }
        bytes20 head = bytes20(bytes32(next * 3));
        bytes4 tail = bytes4(bytes32(~next));
        if (next % 4 == 3) {
            revert Wide(head, tail);
        }
        return saved;
    }

    // A root `bytes4` parameter passed straight to the error (decoded, then re-encoded).
    function lockSelector(bytes4 selector) external returns (uint256) {
        saved = saved + 1;
        if (selector != bytes4(0)) {
            revert LockedSelector(selector);
        }
        return saved;
    }

    function fail() external {
        saved = 99;
        revert LockedSelector(bytes4(0xdeadbeef));
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
