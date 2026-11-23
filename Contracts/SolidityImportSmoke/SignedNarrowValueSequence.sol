// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Narrow signed values from dirty words: `int128(int256(x))` and `int64(w)` truncations, the
// int128 -> uint128 reinterpretation, `type(int128).max` / `.min`, a signed first struct member
// with an unsigned neighbour in the same slot, mappings keyed by int128 and int64 (negative keys
// and keys from truncating casts), int128 / int64 `abi.encodeCall` arguments (values and literals), tuple-literal
// assignments (including a swap) and a `require` without a message.
interface ISignedTarget {
    function f(int128 a, int64 b) external;
}

contract SequenceFixture {
    struct Box {
        int128 low;
        uint128 high;
    }
    mapping(uint256 => Box) private boxes;
    mapping(int128 => uint256) private byWide;
    mapping(int64 => uint256) private byNarrow;
    bytes32 private lastCall;
    uint256 private total;

    function change(uint256 x) external returns (uint256) {
        int128 w = int128(int256(x));
        int64 n = int64(w);
        uint256 k = x % 3;
        boxes[k].high = uint128(x >> 128);
        boxes[k].low = w;
        byWide[w] = byWide[w] + 1;
        byNarrow[n] = x;
        uint256 a;
        uint256 b;
        (a, b) = (uint256(uint128(w)), uint256(uint64(n)));
        (a, b) = (b, a);
        lastCall = keccak256(abi.encodeCall(ISignedTarget.f, (w, n))) ^
            keccak256(abi.encodeCall(ISignedTarget.f, (-1, -2))) ^
            keccak256(abi.encodeCall(ISignedTarget.f, (0, 0)));
        uint256 edges = (w == type(int128).max ? 1 : 0) + (w == type(int128).min ? 2 : 0) +
            (n < 0 ? 4 : 0);
        require(x != 20);
        total = total + (a ^ b) + edges;
        return uint256(int256(boxes[k].low)) ^ uint256(boxes[k].high) ^ byWide[w] ^
            byNarrow[n] ^ uint256(lastCall) ^ total;
    }

    function fail() external {
        boxes[1].low = type(int128).min;
        int128 v = boxes[1].low;
        v = v - 1;
        boxes[1].low = v;
    }

    function read() external view returns (uint256) {
        return total ^ byWide[-1] ^ byNarrow[-1] ^ uint256(int256(boxes[0].low));
    }
}
