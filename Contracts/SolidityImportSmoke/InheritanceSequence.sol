// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

import "./InheritanceBase.sol";

contract SequenceFixture is InheritanceLeft, InheritanceRight {
    uint256 private childValue;

    function computeBonus(uint256 x) internal view override returns (uint256) {
        return leftTouch + rightTouch + childValue + (x % 97) * 3 + 7;
    }

    function step(uint256 x) internal override(InheritanceLeft, InheritanceRight) returns (uint256) {
        return super.step(x);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 seed = input % 100000;
        uint256 direct = InheritanceRoot.step(seed + 5);
        uint256 chained = step(direct);
        uint256 bonus = viaVirtual(seed);
        childValue = chained + bonus;
        emit StepRecorded(chained, bonus);
        require(input != 20, "inheritance rollback");
        return childValue;
    }
}
