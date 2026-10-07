// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    struct Order {
        uint128 amount;
        uint128 fee;
        uint256 epoch;
    }

    uint256 private lockState;
    uint256 private preCounter;
    uint256 private postCounter;
    uint256 private accumulator;
    mapping(uint256 => Order) private orders;
    mapping(uint256 => mapping(uint256 => Order)) private nestedOrders;

    modifier wrapAudit(uint256 tag) {
        require(lockState == 0, "reentrant");
        lockState = 1;
        preCounter += tag + 1;
        _;
        postCounter += tag + 2;
        lockState = 0;
    }

    function _calcPrimary(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * 3 + b + 5;
    }

    function _calcSecondary(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b * 2 + 11;
    }

    function _recordPrimary(uint256 slot, uint256 val) internal {
        orders[slot].epoch = val + 100;
    }

    function _recordSecondary(uint256 slot, uint256 val) internal {
        orders[slot].epoch = val + 200;
    }

    function _splitPair(uint256 x, uint256 y) internal pure returns (uint256, uint256) {
        return (x + 7, y + 9);
    }

    function change(uint256 input) external wrapAudit(input % 17) returns (uint256) {
        uint256 seed = input % 10000;
        uint256 slot = seed % 4;
        uint256 subKey = (seed / 4) % 2;
        bool pickFirst = (seed % 2) == 0;

        function (uint256, uint256) internal pure returns (uint256) calcFn =
            pickFirst ? _calcPrimary : _calcSecondary;
        function (uint256, uint256) internal recordFn =
            pickFirst ? _recordPrimary : _recordSecondary;
        function (uint256, uint256) internal pure returns (uint256, uint256) pairFn =
            _splitPair;

        uint256 computed = calcFn(seed + 1, slot + 2);
        (uint256 p0, uint256 p1) = pairFn(computed, slot);

        Order storage ord = orders[slot];
        ord.amount = uint128((seed % 500) + 10);
        ord.fee = uint128((seed % 50) + 3);
        recordFn(slot, p0);

        nestedOrders[slot][subKey].amount = uint128((seed % 300) + 20);
        nestedOrders[slot][subKey].fee = uint128((seed % 30) + 4);
        nestedOrders[slot][subKey].epoch = p1;

        if ((seed % 3) == 0) {
            delete orders[slot];
        } else if ((seed % 3) == 1) {
            delete nestedOrders[slot][subKey];
        }

        accumulator += computed + orders[slot].amount + orders[slot].fee + orders[slot].epoch
            + nestedOrders[slot][subKey].amount + nestedOrders[slot][subKey].fee + nestedOrders[slot][subKey].epoch;

        require(input != 20, "fnptr struct delete modifier rollback");
        return accumulator + preCounter + postCounter + lockState;
    }

    function fail() external wrapAudit(5) {
        accumulator += 999;
        require(false, "forced revert");
    }

    function read() external view returns (uint256) {
        uint256 ordSum = orders[0].amount + orders[0].fee + orders[0].epoch
            + orders[1].amount + orders[1].fee + orders[1].epoch
            + orders[2].amount + orders[2].fee + orders[2].epoch
            + orders[3].amount + orders[3].fee + orders[3].epoch;
        uint256 nestedSum = nestedOrders[0][0].amount + nestedOrders[0][0].fee + nestedOrders[0][0].epoch
            + nestedOrders[0][1].amount + nestedOrders[0][1].fee + nestedOrders[0][1].epoch
            + nestedOrders[1][0].amount + nestedOrders[1][0].fee + nestedOrders[1][0].epoch
            + nestedOrders[1][1].amount + nestedOrders[1][1].fee + nestedOrders[1][1].epoch
            + nestedOrders[2][0].amount + nestedOrders[2][0].fee + nestedOrders[2][0].epoch
            + nestedOrders[2][1].amount + nestedOrders[2][1].fee + nestedOrders[2][1].epoch
            + nestedOrders[3][0].amount + nestedOrders[3][0].fee + nestedOrders[3][0].epoch
            + nestedOrders[3][1].amount + nestedOrders[3][1].fee + nestedOrders[3][1].epoch;
        return lockState + preCounter + postCounter + accumulator + ordSum + nestedSum;
    }
}
