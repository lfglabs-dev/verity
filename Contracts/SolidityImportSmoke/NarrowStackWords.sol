// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract NarrowStackWords {
    uint256 private first;
    uint256 private second;

    function checkedValue(uint256 x, uint256 n) external pure returns (uint256) {
        uint8 a; uint8 count;
        assembly { a := x count := n }
        return (a >> count) + uint8(1);
    }

    function shiftedCopy(uint256 x, uint256 n) external pure returns (uint256 word) {
        uint8 a; uint8 count;
        assembly { a := x count := n }
        a <<= count;
        uint8 copy = a;
        assembly { word := copy }
    }

    function overwrite(uint256 x, bool reset) external pure returns (uint256 word) {
        uint8 a;
        assembly { a := x }
        unchecked { a += 2; }
        if (reset) a = 7;
        assembly { word := a }
    }

    error NarrowError(uint8 argument);

    function widen(uint8 a) internal pure returns (uint256) { return a; }

    function boundaries(uint256 x) external pure returns (uint8, uint256, uint256) {
        uint8 a;
        assembly { a := x }
        bytes memory payload = abi.encode(a);
        uint256 encoded;
        assembly { encoded := mload(add(payload, 32)) }
        return (a, widen(a), encoded);
    }

    function errorValue(uint256 x) external pure {
        uint8 a;
        assembly { a := x }
        revert NarrowError(a);
    }

    function signedCast(uint256 x) external pure returns (uint256 word) {
        uint8 a;
        assembly { a := x }
        int8 b = int8(a);
        assembly { word := b }
    }

    function carried(uint256 x) external pure returns (uint256 word) {
        uint8 a; uint8 copy;
        assembly { a := x }
        for (uint256 i = 0; i < 2; ++i) {
            copy = a;
            unchecked { a += 2; }
        }
        assembly { word := copy }
    }
}
