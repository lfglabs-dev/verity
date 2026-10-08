// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    event NarrowInitialized(uint8 version);

    uint256 private accumulator;
    uint256 private storedPrimary;
    uint256 private storedSecondary;
    mapping(uint256 => uint256) private claimsByEpoch;
    mapping(uint256 => uint256) private ratesByEpoch;

    function _netGainAfterFees(uint256 gain, uint256 mgmtFee) private pure returns (uint256 netGain) {
        if (mgmtFee >= gain) return netGain;
        gain -= mgmtFee;
        return gain - (gain / 10);
    }

    function _claimAmountsForEpoch(uint256 slot) internal view returns (uint256 claimBasis, uint256 burnAmount) {
        uint256 baseClaim = claimsByEpoch[slot];
        uint256 rate = ratesByEpoch[slot];
        uint256 interest = (baseClaim * rate) / 100;
        claimBasis = baseClaim + interest;
        burnAmount = baseClaim;
    }

    function _clearClaimForEpoch(uint256 slot, uint256 seedBonus) internal returns (uint256 claimBasis, uint256 burnAmount) {
        claimsByEpoch[slot] += seedBonus;
        ratesByEpoch[slot] = (slot + 1) * 5;
        (claimBasis, burnAmount) = _claimAmountsForEpoch(slot);
        if (claimBasis == 0) return (claimBasis, burnAmount);
        claimsByEpoch[slot] -= seedBonus / 2;
        burnAmount += 1;
    }

    function _splitWithParamCompound(uint256 gross, uint256 fee) internal pure returns (uint256, uint256) {
        if (fee >= gross) {
            return (0, gross);
        }
        gross -= fee;
        uint256 boosted = gross;
        boosted += 3;
        return (gross, boosted);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 seed = input % 100000;
        uint256 slot = seed % 4;
        emit NarrowInitialized(type(uint8).max);
        (uint256 clearedBasis, uint256 clearedBurn) = _clearClaimForEpoch(slot, seed + 6);
        (uint256 splitNet, ) = _splitWithParamCompound(seed + 30, (seed % 9) + 4);
        uint256 localSecondary = 0;
        (storedPrimary, localSecondary) = _claimAmountsForEpoch(slot);
        (storedSecondary, ) = _splitWithParamCompound(seed + 25, 7);
        uint256 feeAdjusted = _netGainAfterFees(seed + 50, (seed % 11) + 5);
        accumulator += clearedBasis + clearedBurn + splitNet + localSecondary + feeAdjusted;
        require(input != 20, "tuple helper sequence rollback");
        return accumulator + storedPrimary + storedSecondary + claimsByEpoch[slot];
    }

    function fail() external {
        accumulator += 888;
        require(false, "forced revert");
    }

    function read() external view returns (uint256) {
        return accumulator
            + storedPrimary
            + storedSecondary
            + claimsByEpoch[0] + claimsByEpoch[1] + claimsByEpoch[2] + claimsByEpoch[3]
            + ratesByEpoch[0] + ratesByEpoch[1] + ratesByEpoch[2] + ratesByEpoch[3];
    }
}
