// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Differential mock, compiled by solc only (never imported). Constructor-only
// configuration; every runtime call enters the fallback. A request whose
// calldata differs from the configured length/first word reverts with
// 0xbad0ca11, so selector and argument encoding are observable.
contract CheckedStaticOracle {
    uint256 private value;
    bool private failed;
    uint256 private length;
    uint256 private expected;
    uint256 private expectedLength;

    constructor(uint256 v, bool f, uint256 n, uint256 e, uint256 en) {
        value = v;
        failed = f;
        length = n;
        expected = e;
        expectedLength = en;
    }

    fallback() external {
        uint256 v = value;
        bool f = failed;
        uint256 n = length;
        uint256 e = expected;
        uint256 en = expectedLength;
        assembly ("memory-safe") {
            if or(iszero(eq(calldatasize(), en)), iszero(eq(calldataload(0), e))) {
                mstore(0, shl(224, 0xbad0ca11))
                revert(0, 4)
            }
            mstore(0, v)
            if f { revert(0, n) }
            return(0, n)
        }
    }
}
