pragma solidity 0.8.34;

import {SCALE, FEE, CAP, RATE, LOCK_SLOT, TAG, SMALL, WINDOW, DERIVED, MASK, BIG} from "./SequenceConstants.sol";

contract SequenceFixture {
    uint256 constant LIMIT = CAP * 3;

    uint256 total;
    uint256 last;
    mapping(address => uint256) credit;

    function scaled(uint256 value) internal pure returns (uint256) {
        return value / SCALE * FEE;
    }

    function change(uint256 value) external returns (uint256, uint256, bytes32) {
        require(value < LIMIT || value > BIG, "outside window");
        total = total + scaled(value) + RATE;
        credit[msg.sender] = value >= MASK ? LOCK_SLOT : uint256(TAG);
        last = SMALL * WINDOW + 1 days;
        return (total, 7 weeks - 1 ether / 1e18, TAG);
    }

    function fail() external returns (uint32) {
        require(total > DERIVED, "below derived");
        total = total - DERIVED;
        return RATE;
    }

    function read() external view returns (bool, uint256) {
        return (credit[msg.sender] == LOCK_SLOT, last + CAP);
    }
}
