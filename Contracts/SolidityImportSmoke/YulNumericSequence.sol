// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 indexed result);

    function decimal(uint256 input) internal pure returns (uint256 result) {
        assembly { result := xor(input, 31) }
    }

    function hexadecimal(uint256 input) internal pure returns (uint256 result) {
        assembly { result := xor(input, 0x20) }
    }

    function wordEdge(uint256 input) internal pure returns (uint256 result) {
        assembly {
            result := xor(input, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
        }
    }

    function wrapping(uint256 input) internal pure returns (uint256 result) {
        assembly { result := add(input, 1) }
    }

    function combined(uint256 left, uint256 middle, uint256 right) internal pure returns (uint256 result) {
        assembly { result := xor(xor(left, middle), right) }
    }

    function change(uint256 input) external returns (uint256) {
        uint256 literal = input % 2 == 0 ? decimal(input) : hexadecimal(input);
        uint256 boundary = wordEdge(input);
        uint256 result = combined(wrapping(input), literal, boundary);
        value = result;
        emit Changed(result);
        require(input != 20, "Yul numeric rollback");
        return result;
    }

    function fail() external {
        value = 99;
        emit Changed(99);
        require(false, "Yul numeric failure");
    }

    function read() external view returns (uint256) { return value; }
}
