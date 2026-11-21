// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Inline-assembly `true` and `false` are the words 1 and 0 whatever else the contract
// declares (#2830). The two contracts differ only by one unrelated state variable and one
// unused function.
contract YulBoolLiteralOneSlot {
    uint256 internal stored;

    function flag(uint256 x) external returns (bool r) {
        stored = x;
        assembly { r := true }
    }

    function cleared(uint256 x) external returns (bool r) {
        stored = x;
        assembly { r := false }
    }

    function plusTrue(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly { r := add(x, true) }
    }

    function timesFalse(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly { r := mul(x, false) }
    }

    function boundTrue(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            let t := true
            r := xor(x, t)
        }
    }
}

contract YulBoolLiteralTwoSlots {
    uint256 internal stored;
    uint256 internal unrelated;

    function unused() external { unrelated = 1; }

    function flag(uint256 x) external returns (bool r) {
        stored = x;
        assembly { r := true }
    }

    function cleared(uint256 x) external returns (bool r) {
        stored = x;
        assembly { r := false }
    }

    function plusTrue(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly { r := add(x, true) }
    }

    function timesFalse(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly { r := mul(x, false) }
    }

    function boundTrue(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            let t := true
            r := xor(x, t)
        }
    }
}
