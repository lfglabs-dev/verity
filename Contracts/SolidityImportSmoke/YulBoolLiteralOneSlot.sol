// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Inline-assembly `true` and `false` are the words 1 and 0 whatever else the contract
// declares (#2830). The importer counts state variables across the whole compiled source,
// so each contract of the pair is alone in its file; they differ only by one unrelated
// state variable and one unused function.
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
