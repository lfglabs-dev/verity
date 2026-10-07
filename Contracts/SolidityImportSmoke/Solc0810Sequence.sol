// SPDX-License-Identifier: MIT
pragma solidity 0.8.10;

import './Solc0810Imported.sol';

contract SequenceFixture {
    uint256 private value;
    uint256 private managementFee;
    uint256 private feeSplit;
    event FeeRecorded(uint256 indexed fee, uint256 indexed receiverAmount);

    function change(uint256 input) external returns (uint256) {
        managementFee = (input % 10000) + 1000;
        feeSplit = (input % 50000) + 10000;
        uint256 tvl = (input % 1000000) * 365 days + 365 days;
        uint256 fee = Solc0810Math.calculateManagementFee(tvl, managementFee);
        uint256 receiver = Solc0810Math.feeReceiverAmount(fee, feeSplit);
        value = fee + receiver;
        emit FeeRecorded(fee, receiver);
        require(input != 20, "solc 0.8.10 rollback");
        return value;
    }

    function fail() external {
        value = 99;
        managementFee = 99;
        feeSplit = 99;
        emit FeeRecorded(99, 99);
        require(false, "solc 0.8.10 failure");
    }

    function read() external view returns (uint256) {
        return value + managementFee + feeSplit;
    }
}
