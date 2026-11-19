// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Compound assignment and increment/decrement on narrow signed members of structs held in a
// storage array, including negative stored values: through an indexed element, a storage
// reference and a memory copy; the values of a postfix and a prefix increment; a narrower signed
// member on the right-hand side; checked overflow at the int24 range end and an unchecked wrap.
// One state variable in the whole file, so the import does not depend on the number of state
// variables.
contract SequenceFixture {
    struct Cell {
        int24 t;
        int8 s;
        uint8 tag;
        int16 u;
    }
    Cell[] private cells;
    function change(uint256 x) external returns (int256) {
        if (cells.length < 4) {
            Cell storage fresh = cells.push();
            fresh.tag = 1;
        }
        uint256 k = x % cells.length;
        int24 d = int24(int256((x >> 8) & 0xff) - 128);
        if (((x >> 16) & 1) == 1) {
            cells[k].t = -5;
            cells[k].s = -5;
            cells[k].u = -300;
        }
        if (((x >> 17) & 1) == 1) {
            cells[k].t = type(int24).max - 100;
        }
        cells[k].t += d;
        int24 old = cells[k].t++;
        cells[k].t += cells[k].s;
        cells[k].u -= int16(int256((x >> 24) & 0x7f));
        cells[k].u--;
        if (((x >> 18) & 1) == 1) {
            unchecked {
                cells[k].u -= int16(30000);
                cells[k].u -= int16(30000);
            }
        }
        cells[k].tag += 1;
        Cell storage c = cells[(k + 1) % cells.length];
        c.t -= d;
        c.u++;
        Cell memory m = cells[k];
        m.t -= 1;
        int24 pre = ++m.t;
        int24 copyOld = m.t--;
        m.u += 2;
        return int256(m.t) * 65536 + int256(m.u) + int256(old) * 7 + int256(copyOld) * 11 +
            int256(pre) * 13;
    }
    function fail() external {
        Cell storage c = cells.push();
        c.t = type(int24).min;
        c.t--;
    }
    function read() external view returns (uint256) {
        return cells.length;
    }
}
