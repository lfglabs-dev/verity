// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Reads of narrow signed members of packed storage structs, with negative stored values:
// casts to int256, signed comparisons, checked arithmetic, a storage reference, a memory copy
// and a checked underflow from `type(int24).min`. The same struct is held in a storage array,
// a mapping and a plain state variable, so both struct read paths (raw array slots and
// layout-decoded members) are exercised.
contract SequenceFixture {
    struct Cell {
        int24 t;
        uint8 tag;
        int16 u;
        int128 w;
    }
    Cell[] private cells;
    mapping(uint256 => Cell) private byKey;
    Cell private top;
    function change(uint256 x) external returns (int256) {
        if (cells.length < 3) {
            cells.push();
        }
        uint256 k = x % cells.length;
        int24 a = int24(int256((x >> 8) & 0xffff) - 32768);
        int16 b = int16(int256((x >> 24) & 0xff) - 128);
        int128 c = int128(int256((x >> 32) & 0xffffffff) - 2147483648);
        if (((x >> 64) & 1) == 0) {
            cells[k].t = a;
            cells[k].u = b;
            cells[k].w = c;
            cells[k].tag = uint8(x);
            byKey[k].t = a;
            byKey[k].u = b;
            byKey[k].w = c;
            top.t = a;
            top.u = b;
        }
        int256 acc = int256(cells[k].t);
        if (cells[k].u < 0) {
            acc = acc + 1;
        }
        Cell storage r = cells[(k + 1) % cells.length];
        acc = acc * 3 + int256(r.u) + int256(r.w);
        Cell memory m = cells[k];
        acc = acc * 5 + int256(m.t) - int256(m.w);
        acc = acc * 7 + int256(byKey[k].t) + int256(byKey[k].u);
        if (byKey[k].w < 0) {
            acc = acc - 11;
        }
        acc = acc * 13 + int256(top.t) - int256(top.u);
        int24 sum = cells[k].t + a;
        int16 diff = byKey[k].u - b;
        return acc * 17 + int256(sum) + int256(diff);
    }
    function fail() external {
        Cell storage c = cells.push();
        c.t = type(int24).min;
        int24 v = c.t - 1;
        c.t = v;
    }
    function read() external view returns (uint256) {
        return cells.length;
    }
}
