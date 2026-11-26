// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). It calls its caller back once per
// call, so a campaign can exercise a real re-entrant callback. Slot 0 holds the callback
// selector, slot 1 the argument count (0..3), slots 2..4 the argument words, slot 5 the flags,
// and slot 6 counts the answered calls.
//
// Flags:
//   bit 0 (1): revert with no data after a successful callback (or inert call).
//   bit 1 (2): inert callee (skip calling back, still count the call, then return/revert).
//   bit 2 (4): read-only view responder (write no storage, return `arg0` as one 32-byte word;
//              answers `STATICCALL` as well as `CALL`).
//
// Every runtime call enters the fallback. Without bit 2, it increments slot 6, then (unless
// bit 1 is set) calls `msg.sender` without value with the payload (the four selector bytes,
// followed by `argumentCount` 32-byte argument words). A failed callback is bubbled with its
// exact return data. Either revert rolls back the counter and everything the callback wrote.
contract ReentrantCallbackHook {
    constructor(
        uint256 selector,
        uint256 argumentCount,
        uint256 arg0,
        uint256 arg1,
        uint256 arg2,
        uint256 flags
    ) {
        require(selector < 2 ** 32 && argumentCount <= 3);
        assembly {
            sstore(0, selector)
            sstore(1, argumentCount)
            sstore(2, arg0)
            sstore(3, arg1)
            sstore(4, arg2)
            sstore(5, flags)
        }
    }

    fallback() external {
        assembly {
            let selector := sload(0)
            let argumentCount := sload(1)
            let arg0 := sload(2)
            let arg1 := sload(3)
            let arg2 := sload(4)
            let flags := sload(5)
            if and(flags, 4) {
                mstore(0, arg0)
                return(0, 32)
            }
            sstore(6, add(sload(6), 1))
            if iszero(and(flags, 2)) {
                mstore(0, shl(224, selector))
                mstore(4, arg0)
                mstore(36, arg1)
                mstore(68, arg2)
                let ok := call(gas(), caller(), 0, 0, add(4, mul(32, argumentCount)), 0, 0)
                if iszero(ok) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
            }
            if and(flags, 1) { revert(0, 0) }
            return(0, 0)
        }
    }
}
