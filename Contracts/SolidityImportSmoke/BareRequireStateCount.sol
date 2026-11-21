// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `require(bool)` without a message must lower the same way whatever else the
// contract declares (#2830). The two contracts differ only by one unrelated
// state variable and one unused function.
contract BareRequireOneSlot {
    uint256 internal stored;

    function voidGuard(uint256 n) internal pure { require(n != 20); }

    function namedGuard(uint256 n) internal pure returns (uint256 result) {
        result = n + 1;
        require(n != 30);
    }

    function rootGuard(uint256 x) external returns (uint256) {
        require(x != 20);
        stored = x;
        return stored;
    }

    function helperGuard(uint256 x) external returns (uint256) {
        voidGuard(x);
        stored = x;
        return stored;
    }

    function namedHelperGuard(uint256 x) external pure returns (uint256) {
        return namedGuard(x);
    }
}

contract BareRequireTwoSlots {
    uint256 internal stored;
    uint256 internal unrelated;

    function unused() external { unrelated = 1; }

    function voidGuard(uint256 n) internal pure { require(n != 20); }

    function namedGuard(uint256 n) internal pure returns (uint256 result) {
        result = n + 1;
        require(n != 30);
    }

    function rootGuard(uint256 x) external returns (uint256) {
        require(x != 20);
        stored = x;
        return stored;
    }

    function helperGuard(uint256 x) external returns (uint256) {
        voidGuard(x);
        stored = x;
        return stored;
    }

    function namedHelperGuard(uint256 x) external pure returns (uint256) {
        return namedGuard(x);
    }
}
