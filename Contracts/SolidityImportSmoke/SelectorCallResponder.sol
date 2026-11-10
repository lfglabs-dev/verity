// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). The constructor stores a table of
// at most eight entries of seven words each: selector, flags, response length (at most 128)
// and four response words. Every runtime call enters the fallback, which answers with the first
// entry whose selector matches the first four calldata bytes and reverts with no data when none
// does. Flag bit 0 makes the answer a revert. Flag bit 1 marks a view entry, answered without
// writing storage, so a `staticcall` gets it too. A non-view entry first increments the call
// counter in slot 1 and records the calldata size and first four calldata words in slots 2..6;
// a failing answer rolls those writes back. Slot 0 holds the entry count; entry i starts at
// slot 16 + 8 i.
contract SelectorCallResponder {
    constructor(uint256[] memory table) {
        uint256 n = table.length / 7;
        require(table.length % 7 == 0 && n <= 8);
        assembly {
            sstore(0, n)
        }
        for (uint256 i = 0; i < n; i++) {
            require(table[7 * i + 2] <= 128);
            for (uint256 j = 0; j < 7; j++) {
                uint256 word = table[7 * i + j];
                uint256 slot = 16 + 8 * i + j;
                assembly {
                    sstore(slot, word)
                }
            }
        }
    }

    fallback() external {
        assembly {
            let selector := shr(224, calldataload(0))
            let n := sload(0)
            let base := 0
            for { let i := 0 } lt(i, n) { i := add(i, 1) } {
                let entry := add(16, mul(i, 8))
                if and(iszero(base), eq(sload(entry), selector)) { base := entry }
            }
            if iszero(base) { revert(0, 0) }
            let flags := sload(add(base, 1))
            let size := sload(add(base, 2))
            if iszero(and(flags, 2)) {
                sstore(1, add(sload(1), 1))
                sstore(2, calldatasize())
                sstore(3, calldataload(0))
                sstore(4, calldataload(32))
                sstore(5, calldataload(64))
                sstore(6, calldataload(96))
            }
            mstore(0, sload(add(base, 3)))
            mstore(32, sload(add(base, 4)))
            mstore(64, sload(add(base, 5)))
            mstore(96, sload(add(base, 6)))
            if and(flags, 1) { revert(0, size) }
            return(0, size)
        }
    }
}
