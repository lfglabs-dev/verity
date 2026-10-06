// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library DiscardedHelperLib {
    function checked(uint256 value) internal pure returns (uint256) {
        require(value != 40, "discarded library");
        return value + 1;
    }
}

contract SequenceFixture {
    uint256 public value;
    event Changed(uint256 value);

    function bump(uint256 input) internal returns (uint256) {
        value = value + input;
        emit Changed(value);
        if (input == 30) return value;
        require(input != 20, "discarded helper");
        value = value + 1;
        return value;
    }

    function change(uint256 input) external returns (uint256) {
        bump(input);
        DiscardedHelperLib.checked(input);
        value = value + 10;
        emit Changed(value);
        return value;
    }

    function fail() external returns (uint256) {
        bump(1);
        require(false, "discarded rollback");
        return value;
    }

    function read() external view returns (uint256) { return value; }
}
