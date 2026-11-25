// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). Constructor-only
// configuration; every runtime call enters the fallback. Writes up to three
// 32-byte words into fresh memory at 0x80..0xdf (word0 XORed with
// calldataFold & mask) and returns or reverts `length` bytes, so multi-return
// ABI decoding (valid, dirty narrow words, short returndata, extra bytes,
// revert forwarding) and calldata folding are all observable across A/B/C.
contract MultiWordStaticOracle {
    uint256 private word0;
    uint256 private word1;
    uint256 private word2;
    bool private failed;
    uint256 private length;
    uint256 private mask;

    constructor(uint256 w0, uint256 w1, uint256 w2, bool f, uint256 n, uint256 m) {
        word0 = w0;
        word1 = w1;
        word2 = w2;
        failed = f;
        length = n;
        mask = m;
    }

    fallback() external {
        uint256 w0 = word0;
        uint256 w1 = word1;
        uint256 w2 = word2;
        bool f = failed;
        uint256 n = length;
        uint256 m = mask;
        assembly ("memory-safe") {
            let size := calldatasize()
            let acc := add(mul(size, 31), shr(224, calldataload(0)))
            for { let offset := 4 } lt(offset, size) { offset := add(offset, 32) } {
                acc := add(mul(acc, 31), calldataload(offset))
            }
            mstore(0x80, xor(w0, and(acc, m)))
            mstore(0xa0, w1)
            mstore(0xc0, w2)
            if f { revert(0x80, n) }
            return(0x80, n)
        }
    }
}
