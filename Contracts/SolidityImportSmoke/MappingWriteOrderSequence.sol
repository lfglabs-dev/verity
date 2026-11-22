// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// solc (legacy and via-IR) evaluates an assignment's right-hand side before the target's
// mapping keys and array indexes, for `=` and `op=`; the target's bounds check comes after
// the right-hand side. change(x) selects one assignment by x % 16 and drives it with
// y = x / 16: y = 0 makes both the key (`y - 1`) and the right-hand side (`10 / y`) revert,
// so the panic code shows which ran first; `bump` is a key helper that writes the stamp the
// right-hand side reads; `restamp` is a right-hand-side helper that writes the stamp the key
// reads, so key-first evaluation writes a different slot.
contract SequenceFixture {
    struct Book {
        mapping(uint256 => uint256) slots;
        uint256[] vals;
    }

    uint256[] internal arr;
    mapping(uint256 => uint256) internal m;
    mapping(uint256 => mapping(uint256 => uint256)) internal mm;
    mapping(uint256 => Book) internal books;
    uint256 internal stamp;

    event Written(uint256 selector, uint256 stamp);

    function bump(uint256 v) internal returns (uint256) {
        stamp = stamp * 10 + 1;
        return v;
    }

    function restamp() internal returns (uint256) {
        stamp = 2;
        return 7;
    }

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 16;
        uint256 y = x / 16;
        uint256 k = y % 4;
        stamp = 5;
        if (arr.length == 0) {
            arr.push();
            arr.push();
            arr.push();
            arr.push();
        }
        if (books[1].vals.length == 0) {
            books[1].vals.push();
            books[1].vals.push();
            books[1].vals.push();
            books[1].vals.push();
        }
        // Storage dynamic array element.
        if (c == 0) { arr[y - 1] = 10 / y; }
        if (c == 1) { arr[bump(k)] = stamp + 100; }
        // Mapping and nested mapping value.
        if (c == 2) { m[y - 1] = 10 / y; }
        if (c == 3) { m[bump(k)] = stamp + 100; }
        if (c == 4) { m[stamp + k] = restamp(); }
        if (c == 5) { mm[y - 1][1] = 10 / y; }
        if (c == 6) { mm[bump(k)][1] = stamp + 100; }
        if (c == 7) { mm[stamp + k][1] = restamp(); }
        // Mapping compound assignment: right-hand side, key, read, combine.
        if (c == 8) { m[y - 1] += 10 / y; }
        if (c == 9) { m[bump(k)] += stamp + 100; }
        // Struct-member mapping and dynamic array element (13: `op=` control).
        if (c == 10) { books[1].slots[y - 1] = 10 / y; }
        if (c == 11) { books[1].vals[y - 1] = 10 / y; }
        if (c == 12) { books[1].vals[bump(k)] = stamp + 100; }
        if (c == 13) { books[1].slots[y - 1] += 10 / y; }
        // Controls: dynamic array compound assignment and a pure computed key.
        if (c == 14) { arr[y - 1] += 10 / y; }
        if (c == 15) { m[y % 4] = stamp + y; }
        emit Written(c, stamp);
        return stamp;
    }

    function fail() external {
        stamp = 123;
        require(false, "write order rollback");
    }

    function read() external view returns (uint256) {
        return stamp + arr.length;
    }
}
