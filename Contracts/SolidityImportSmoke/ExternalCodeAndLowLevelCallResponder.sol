// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). Constructor-only
// configuration; every runtime call enters the fallback, which increments the
// call counter and records the calldata size and first four calldata words
// before answering, so selector and argument encoding are observable in storage.
// A failed response rolls the records back.
contract RecordingCallResponder {
    uint256 private value;
    bool private failed;
    uint256 private length;
    uint256 private calls;
    uint256 private size;
    bytes32[4] private words;

    constructor(uint256 v, bool f, uint256 n) {
        value = v;
        failed = f;
        length = n;
    }

    fallback() external {
        uint256 v = value;
        bool f = failed;
        uint256 n = length;
        calls += 1;
        assembly ("memory-safe") {
            sstore(size.slot, calldatasize())
            sstore(add(words.slot, 0), calldataload(0))
            sstore(add(words.slot, 1), calldataload(32))
            sstore(add(words.slot, 2), calldataload(64))
            sstore(add(words.slot, 3), calldataload(96))
            mstore(0, v)
            if f { revert(0, n) }
            return(0, n)
        }
    }
}
