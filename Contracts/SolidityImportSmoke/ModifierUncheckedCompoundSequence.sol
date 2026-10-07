// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    struct Ledger {
        uint128 credit;
        uint128 debit;
    }

    uint256 private accumulator;
    uint64 private rollingWrap;
    uint64 private modifierTicks;
    uint256 private lastAssigned;
    mapping(uint256 => uint256) private buckets;
    mapping(uint256 => Ledger) private ledgers;

    modifier guardAndTick(uint256 raw) {
        require(raw != 19, "modifier rejected input");
        modifierTicks += 1;
        _;
    }

    modifier helperTick(uint64 delta) {
        modifierTicks += delta;
        _;
    }

    function syncPublic(uint256 seed) public helperTick(2) {
        uint256 slot = seed % 4;
        buckets[slot] += seed + (10 ** 3);
        ledgers[slot].credit += uint128(seed + 5);
    }

    function _uncheckedHelper(uint256 seed) internal returns (uint256) {
        uint256 slot = seed % 4;
        uint256 localAcc = seed + (2 ** 8);
        localAcc += 17;
        localAcc -= 5;
        unchecked {
            rollingWrap -= uint64(seed + 1);
            ledgers[slot].debit -= uint128(seed + 3);
        }
        uint256 assigned = ((lastAssigned = localAcc + 9) == 0) ? 1 : (lastAssigned + 4);
        return assigned + uint256(rollingWrap);
    }

    function change(uint256 input) external guardAndTick(input) returns (uint256) {
        uint256 seed = input % 100000;
        syncPublic(seed);
        uint256 helperOut;
        unchecked {
            uint256 wrapMul = (type(uint256).max - seed) * 3;
            uint256 rawHelper = _uncheckedHelper(seed);
            helperOut = rawHelper + (wrapMul % 256);
        }
        uint256 localMirror = 0;
        uint256 echoed = (localMirror = seed + 11) + 6;
        accumulator += helperOut + echoed + localMirror;
        require(input != 20, "modifier unchecked compound rollback");
        return accumulator + buckets[seed % 4] + uint256(ledgers[seed % 4].credit) + uint256(modifierTicks);
    }

    function fail() external {
        accumulator += 777;
        require(false, "forced revert");
    }

    function read() external view returns (uint256) {
        return accumulator
            + uint256(rollingWrap)
            + uint256(modifierTicks)
            + lastAssigned
            + buckets[0] + buckets[1] + buckets[2] + buckets[3]
            + uint256(ledgers[0].credit) + uint256(ledgers[1].credit)
            + uint256(ledgers[0].debit) + uint256(ledgers[1].debit);
    }
}
