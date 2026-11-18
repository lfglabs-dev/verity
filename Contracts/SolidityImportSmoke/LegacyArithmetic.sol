// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library LegacyArithmeticHelpers {
    /// The helper boundary must preserve the selected arithmetic default.
    function add(uint8 x, uint8 y) internal pure returns (uint8) {
        return x + y;
    }

    function nested(uint8 x, uint8 y) internal pure returns (uint8) {
        return add(x, y);
    }

    function divide(uint256 x, uint256 y) internal pure returns (uint256) {
        return x / y;
    }
}

contract LegacyArithmetic {
    uint256 private stored;

    /// Exercise wide and narrow arithmetic in the same root.
    function arithmetic(uint256 x, uint256 y) external pure
        returns (uint256, uint256, uint256, uint8, uint16, uint128)
    {
        return (x + y, x - y, x * y, uint8(x) + uint8(y),
            uint16(x) - uint16(y), uint128(x) * uint128(y));
    }

    function helper(uint256 x, uint256 y) external pure returns (uint256) {
        return uint256(LegacyArithmeticHelpers.nested(uint8(x), uint8(y)));
    }

    function wrapThenCheck(uint256 x, uint256 y) external pure returns (uint256) {
        uint256 sum = x + y;
        require(sum >= x, "overflow");
        return sum;
    }

    function scalarAbi(uint8 x, bool flag, address recipient) external pure
        returns (uint256, bool, address)
    {
        return (uint256(x), flag, recipient);
    }

    function division(uint256 x, uint256 y) external pure returns (uint256) {
        return x / y;
    }

    function helperDivision(uint256 x, uint256 y) external pure returns (uint256) {
        return LegacyArithmeticHelpers.divide(x, y);
    }

    function modulo(uint256 x, uint256 y) external pure returns (uint256) {
        return x % y;
    }

    function assertion(uint256 x, uint256 y) external pure returns (uint256) {
        assert(x >= y);
        return x;
    }

    function mutation(uint256 x, uint256) external returns (uint256) {
        stored = x;
        return stored;
    }

    function fixedBytesConversion(uint256 x, uint256) external pure returns (bytes32) {
        return bytes32(x);
    }
}
