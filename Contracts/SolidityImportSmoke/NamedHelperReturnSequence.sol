// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 indexed result);

    function defaultResult() internal pure returns (uint256 result) { }

    function early(uint256 input) internal returns (uint256 result) {
        value = input;
        emit Changed(input);
        if (input == 30) return result;
        result = input + 2;
        if (input % 2 == 0) return result;
        result = result + 3;
    }

    function continuedAssembly(uint256 input) internal pure returns (uint256 result) {
        assembly { result := xor(input, mul(input, lt(input, input))) }
        require(input != 20, "named assembly continuation");
        result = result + 1;
    }

    function narrowAssembly(uint256 input) internal pure returns (uint8 result) {
        assembly { result := xor(input, mul(input, lt(input, input))) }
        require(input != 40, "named narrow continuation");
        return result;
    }

    function nested(uint256 input) internal pure returns (uint256 result) {
        result = input + 9;
        uint256 zero = defaultResult();
        result = result + zero;
    }

    function booleanAssembly(uint256 input) internal pure returns (bool result) {
        assembly { result := xor(input, mul(input, lt(input, input))) }
        require(input != 50, "named bool continuation");
        return result;
    }

    function addressAssembly(uint256 input) internal pure returns (address result) {
        assembly { result := xor(input, mul(input, lt(input, input))) }
        require(input != 60, "named address continuation");
        return result;
    }

    function branchAssembly(uint256 input) internal pure returns (uint256 result) {
        if (input % 2 == 0) {
            assembly { result := xor(input, mul(input, lt(input, input))) }
        } else {
            result = input + 4;
        }
        require(input != 70, "named branch continuation");
        result = result + 5;
    }

    function shadowedAssembly(uint256 input) internal pure returns (uint256 result) {
        uint256 seed = input + 2;
        result = 7;
        if (input % 2 == 0) {
            uint256 result = seed;
            result = result + 1;
        } else {
            uint256 input = seed;
            assembly { result := add(result, input) }
        }
        assembly { result := add(result, xor(input, mul(input, lt(input, input)))) }
        result = result + 6;
    }

    function change(uint256 input) external returns (uint256) {
        uint256 zero = defaultResult();
        uint256 first = early(input);
        uint256 second = continuedAssembly(input);
        uint256 narrow = narrowAssembly(input);
        uint256 third = nested(input);
        bool flag = booleanAssembly(input);
        if (flag) require(flag == true, "named bool cleanup");
        address who = addressAssembly(input);
        uint256 addressValue = uint256(uint160(who));
        uint256 booleanValue = flag ? 1 : 0;
        uint256 branchValue = branchAssembly(input);
        uint256 shadowedValue = shadowedAssembly(input);
        value = zero + first + second + narrow + third + addressValue + booleanValue + branchValue + shadowedValue;
        emit Changed(value);
        return value;
    }

    function fail() external {
        uint256 first = early(1);
        value = first;
        require(false, "named caller rollback");
    }

    function read() external view returns (uint256) { return value; }
}
