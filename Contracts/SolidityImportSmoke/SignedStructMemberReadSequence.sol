// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Reads of narrow signed members of packed storage structs, with negative stored values:
// casts to int256, signed comparisons, checked arithmetic, a storage reference, a memory copy,
// a checked underflow from `type(int24).min` and the raw stack words inline assembly reads. The
// same struct is held in a storage array, a mapping and a plain state variable, so both struct read
// paths (raw array slots and layout-decoded members) are exercised.
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
        // Bit 65 stores values that use each member's top byte (|a| * 255 up to 2^23, |b| * 255
        // up to 2^15, c * 2^96 up to 2^127): a sign extension one byte short differs on them.
        int24 sa = a;
        int16 sb = b;
        int128 sc = c;
        if (((x >> 65) & 1) == 1) {
            sa = int24(int256(a) * 255);
            sb = int16(int256(b) * 255);
            sc = int128(int256(c) * 2 ** 96);
        }
        if (((x >> 64) & 1) == 0) {
            cells[k].t = sa;
            cells[k].u = sb;
            cells[k].w = sc;
            cells[k].tag = uint8(x);
            byKey[k].t = sa;
            byKey[k].u = sb;
            byKey[k].w = sc;
            byKey[k].tag = uint8(x);
            top.t = sa;
            top.u = sb;
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
        // The unsigned neighbour member stays zero-extended (tag >= 128 in the prefix).
        acc = acc * 19 + int256(uint256(cells[k].tag)) + int256(uint256(byKey[k].tag)) +
            int256(uint256(m.tag));
        return acc * 17 + int256(sum) + int256(diff);
    }
    function fail() external {
        Cell storage c = cells.push();
        c.t = type(int24).min;
        int24 v = c.t - 1;
        c.t = v;
    }
    // Inline assembly sees each read's stack word as solc leaves it: sign-extended, on the raw
    // array path (`cells`) and on the layout path (`byKey`, `top`).
    function read() external view returns (uint256 n, uint256 wordT, uint256 wordU, uint256 wordTop) {
        n = cells.length;
        int24 stackT = n > 0 ? cells[0].t : int24(0);
        int16 stackU = byKey[0].u;
        int24 stackTop = top.t;
        assembly {
            wordT := stackT
            wordU := stackU
            wordTop := stackTop
        }
    }
}
