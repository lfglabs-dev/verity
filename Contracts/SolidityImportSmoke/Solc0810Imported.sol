// SPDX-License-Identifier: MIT
pragma solidity 0.8.10;

library Solc0810Math {
    uint256 internal constant ONE_YEAR = 365 days;
    uint256 internal constant FULL_ALLOC = 100000;

    function calculateManagementFee(uint256 totalTVL, uint256 feeApr) internal pure returns (uint256) {
        return (totalTVL * feeApr) / (ONE_YEAR * FULL_ALLOC);
    }

    function feeReceiverAmount(uint256 amount, uint256 feeSplit) internal pure returns (uint256) {
        return (amount * feeSplit) / FULL_ALLOC;
    }
}
