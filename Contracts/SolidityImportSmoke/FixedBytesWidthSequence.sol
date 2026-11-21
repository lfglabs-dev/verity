// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    bytes32 private acc;
    bytes32 private seen;

    function _prefix(uint256 x) internal pure returns (bytes19) {
        return bytes19(uint152(uint160(x) >> 8));
    }

    function change(uint256 x) external returns (bytes32) {
        bytes19 p = _prefix(x);
        bytes1 q = bytes1(uint8(x));
        bytes31 r = bytes31(p);
        bytes19 s = bytes19(bytes32(x));
        bytes7 t = bytes7(r);
        bytes4 f = bytes4(s);
        uint152 u = uint152(p);
        uint248 w = uint248(bytes31(bytes32(x)));
        bool same = bytes19(r) == p;
        acc = bytes32(r) ^ bytes32(s) ^ bytes32(t) ^ bytes32(f) ^ bytes32(q) ^
            bytes32(uint256(u) + uint256(w) + (same ? 1 : 0));
        return acc;
    }

    function fail() external {
        acc = bytes32(bytes19(uint152(7)));
        revert();
    }

    function read() external view returns (bytes32, bytes32) {
        return (acc, seen);
    }

    function widths(bytes1 a, bytes19 b, bytes31 c) external returns (bytes1, bytes19, bytes31) {
        seen = bytes32(a) ^ bytes32(b) ^ bytes32(c);
        return (a, bytes19(c), bytes31(b));
    }

    function nibble(bytes1 ch) external pure returns (bool, uint8) {
        uint8 v = uint8(ch);
        if (47 < v && v < 58) {
            return (true, v - 48);
        }
        if (96 < v && v < 103) {
            return (true, v - 87);
        }
        return (false, 0);
    }
}
