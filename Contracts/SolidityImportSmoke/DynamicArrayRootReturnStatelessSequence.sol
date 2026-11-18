// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// No state variables: the importer's `stateVars.size > 1` gates are all off,
// so this runs the stateless lowering of dynamic root return tuples (#2707):
// a named `T[]` beside a scalar, a lone `T[]`, and `bytes`/`string` components.
contract SequenceFixture {
    function window(uint256 x) internal pure returns (uint256[] memory w) {
        w = new uint256[](x % 3);
        for (uint256 i = 0; i < w.length; ++i) {
            w[i] = x + i;
        }
    }

    function change(uint256 x) external pure returns (uint256[] memory items, uint256 next) {
        next = x % 5;
        if (next == 0) return (items, next);
        items = window(x);
        uint8[] memory narrow = new uint8[](1);
        narrow[0] = uint8(x);
        uint8 low = narrow[0];
        if (next == 4) return (new uint256[](next), low);
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external pure returns (uint256[] memory) {
        return window(7);
    }

    // A root `T[] memory` parameter returned as is: ABI-decoded (each element
    // checked against `uint8`) and re-encoded.
    function echoNarrow(uint8[] memory xs) external pure returns (uint8[] memory) {
        return xs;
    }

    function labelled() external pure returns (string memory name, bool[] memory flags, bytes memory tag) {
        name = "flags";
        flags = new bool[](2);
        flags[1] = true;
        tag = abi.encodePacked(uint16(0xbeef));
    }
}
