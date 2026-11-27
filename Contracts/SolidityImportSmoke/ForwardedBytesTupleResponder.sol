// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

// Differential mock, compiled by solc only (never imported). Answers any CALL
// with raw bytes from slots 0..5 (up to 192 bytes, truncated to slot 6 `retLen`).
//
// Storage layout:
//   slots 0..5 : raw response words (big-endian 32-byte words)
//   slot 6     : retLen (0..192)
//   slot 7     : flags
//                  bit 0 (1): revert with `retLen` bytes instead of returning
//                  bit 1 (2): re-enter `msg.sender` with 4-byte `cbSelector` (slot 8)
//                             before answering; bubble callback revert if it fails
//                  bit 2 (4): pass 1 word `cbArg0` (slot 9) after `cbSelector` (36-byte callback)
//   slot 8     : cbSelector (4-byte selector, right-aligned)
//   slot 9     : cbArg0
//   slot 10    : call counter (incremented on every call; rolled back on revert)
//   slot 11    : last calldatasize()
//   slot 12    : last calldataload(0)
contract ForwardedBytesTupleResponder {
    constructor(
        uint256 w0,
        uint256 w1,
        uint256 w2,
        uint256 w3,
        uint256 w4,
        uint256 w5,
        uint256 retLen,
        uint256 flags,
        uint256 cbSelector,
        uint256 cbArg0
    ) {
        require(retLen <= 192 && cbSelector < 2 ** 32);
        assembly {
            sstore(0, w0)
            sstore(1, w1)
            sstore(2, w2)
            sstore(3, w3)
            sstore(4, w4)
            sstore(5, w5)
            sstore(6, retLen)
            sstore(7, flags)
            sstore(8, cbSelector)
            sstore(9, cbArg0)
        }
    }

    fallback() external {
        assembly {
            sstore(10, add(sload(10), 1))
            sstore(11, calldatasize())
            sstore(12, calldataload(0))
            let flags := sload(7)
            if and(flags, 2) {
                let sel := sload(8)
                mstore(0, shl(224, sel))
                let cbSize := 4
                if and(flags, 4) {
                    mstore(4, sload(9))
                    cbSize := 36
                }
                let ok := call(gas(), caller(), 0, 0, cbSize, 0, 0)
                if iszero(ok) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
            }
            mstore(0, sload(0))
            mstore(32, sload(1))
            mstore(64, sload(2))
            mstore(96, sload(3))
            mstore(128, sload(4))
            mstore(160, sload(5))
            let len := sload(6)
            if and(flags, 1) {
                revert(0, len)
            }
            return(0, len)
        }
    }
}
