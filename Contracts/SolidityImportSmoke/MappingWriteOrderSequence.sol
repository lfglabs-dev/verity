// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// solc (legacy and via-IR) evaluates an assignment's right-hand side before the target's
// mapping keys and array indexes, for `=` and `op=`; the target's bounds check comes after
// the right-hand side. change(x) selects one assignment by x % 16 and drives it with
// y = x / 16: y = 0 makes both the key (`y - 1`) and the right-hand side (`10 / y`) revert,
// so the panic code shows which ran first; `bump` is a key helper that writes the stamp the
// right-hand side reads; `restamp` is a right-hand-side helper that writes the stamp the key
// reads, so key-first evaluation writes a different slot; `i++` in an index with the bare
// local `i` as the right-hand side checks that the right-hand side is captured before it.
contract SequenceFixture {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    struct Book {
        mapping(uint256 => uint256) slots;
        uint256[] vals;
    }

    uint256[] internal arr;
    mapping(uint256 => uint256) internal m;
    mapping(uint256 => mapping(uint256 => uint256)) internal mm;
    mapping(uint256 => Book) internal books;
    Pair[] internal pairs;
    mapping(uint256 => Pair) internal held;
    uint256 internal stamp;

    event Written(uint256 selector, uint256 stamp);

    function bump(uint256 v) internal returns (uint256) {
        stamp = stamp * 10 + 1;
        return v;
    }

    function touchHeld(uint256 v) internal returns (uint256) {
        held[0].a = held[0].a + 1;
        return v;
    }

    function heldZero() internal view returns (Pair storage) {
        return held[0];
    }

    function viewPair() internal view returns (Pair memory) {
        return Pair(stamp, stamp + 1);
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
        if (pairs.length == 0) {
            pairs.push();
            pairs.push();
            pairs.push();
            pairs.push();
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
        // Struct-member mapping and dynamic array element (13: `op=`, constant and `j5++` keys).
        if (c == 10) { books[1].slots[y - 1] = 10 / y; }
        if (c == 11) { books[1].vals[y - 1] = 10 / y; }
        if (c == 12) {
            books[1].vals[bump(k)] = stamp + 100;
            // A storage struct source is read at the copy, after the key helper.
            held[touchHeld(k + 1)] = held[0];
            // A helper result and a conditional of constructors are values: evaluated first.
            held[bump(k + 4)] = viewPair();
            held[bump(k + 8)] = y > 1 ? Pair(stamp, 1) : Pair(2, stamp);
            held[bump(k + 12)] = (Pair(stamp, 3));
            held[bump(k + 16)] = y > 1 ? (y > 2 ? Pair(stamp, 4) : Pair(4, stamp)) : Pair(stamp, 5);
            // A storage pointer helper is a reference: read after the key helper.
            held[touchHeld(k + 20)] = heldZero();
            // A storage branch of a memory conditional is copied before the key helper.
            held[touchHeld(k + 24)] = y > 0 ? held[0] : Pair(1, 2);
        }
        if (c == 13) {
            books[1].slots[y - 1] += 10 / y;
            uint256 j5 = k;
            books[j5++].slots[0] += j5;
        }
        // Dynamic array compound assignment: the right-hand side was already first.
        if (c == 14) {
            arr[y - 1] += 10 / y;
            uint256 i1 = k;
            arr[i1++] += i1;
            uint256 i2 = k;
            books[1].vals[i2++] += i2;
        }
        // A pure computed key (unchanged), then `i++` indexes with a bare-local right-hand side.
        if (c == 15) {
            m[y % 4] = stamp + y;
            uint256 j1 = k;
            m[j1++] = j1;
            uint256 j2 = k;
            arr[j2++] = j2;
            uint256 j3 = k;
            pairs[j3++].a = j3;
            uint256 j4 = k;
            pairs[j4++].b += j4;
            // Whole-struct write: the constructor arguments run before the key.
            uint256 j6 = k;
            held[j6++] = Pair(j6, j6);
            held[y - 1] = Pair(10 / y, 1);
        }
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
