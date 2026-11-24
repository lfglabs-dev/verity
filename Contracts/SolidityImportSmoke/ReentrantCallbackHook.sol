// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). It calls its caller back once per
// call, so a campaign can exercise a real re-entrant callback. Slot 0 holds the callback
// selector, slot 1 the argument count (0 or 1), slot 2 the argument word and slot 3 the flags;
// slot 4 counts the answered calls. Every runtime call enters the fallback, which reads slots
// 0..3, increments slot 4, then calls `msg.sender` without value with the payload (the four
// selector bytes, then the argument word if there is one). A failed callback is bubbled: the
// fallback reverts with the callback's exact return data. With flag bit 0 set, the fallback
// reverts with no data after a successful callback; otherwise it returns no data. Either revert
// rolls back the counter and everything the callback wrote.
contract ReentrantCallbackHook {
    constructor(uint256 selector, uint256 argumentCount, uint256 argument, uint256 flags) {
        require(selector < 2 ** 32 && argumentCount <= 1);
        assembly {
            sstore(0, selector)
            sstore(1, argumentCount)
            sstore(2, argument)
            sstore(3, flags)
        }
    }

    fallback() external {
        assembly {
            let selector := sload(0)
            let argumentCount := sload(1)
            let argument := sload(2)
            let flags := sload(3)
            sstore(4, add(sload(4), 1))
            mstore(0, shl(224, selector))
            mstore(4, argument)
            let ok := call(gas(), caller(), 0, 0, add(4, mul(32, argumentCount)), 0, 0)
            if iszero(ok) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            if and(flags, 1) { revert(0, 0) }
            return(0, 0)
        }
    }
}
