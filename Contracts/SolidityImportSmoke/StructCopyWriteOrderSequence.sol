// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// solc (legacy and via-IR) evaluates an assignment's right-hand side before the target's keys.
// A `string` value is built first. A storage struct source is a reference: solc evaluates its
// slot (its own keys and index check, a storage-pointer helper call) before the target's keys
// and reads its members at the copy, after them. change(x) selects one case by x % 8 and drives
// it with y = x / 8: y = 0 makes both the target key (`y - 1`) and the right-hand side
// (`10 / y`) revert, so the panic code shows which ran first; `bump` is a key helper that writes
// the stamp the right-hand side reads; `touchPairs` / `touchHeld` are key helpers that write the
// source struct; `i++` / `cursor++` in a target key change the source's own key.
contract SequenceFixture {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    mapping(uint256 => string) internal labels;
    Pair[] internal pairs;
    mapping(uint256 => Pair) internal held;
    mapping(uint256 => mapping(uint256 => Pair)) internal grid;
    uint256 internal stamp;
    uint256 internal cursor;
    uint256 internal out;

    event Written(uint256 selector, uint256 out);

    function bump(uint256 v) internal returns (uint256) {
        stamp = stamp * 10 + 1;
        return v;
    }

    function touchPairs(uint256 v) internal returns (uint256) {
        pairs[0].a = pairs[0].a + 7;
        return v;
    }

    function touchHeld(uint256 v) internal returns (uint256) {
        held[0].a = held[0].a + 7;
        return v;
    }

    function heldAt(uint256 i) internal view returns (Pair storage) {
        return held[i];
    }

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 8;
        uint256 y = x / 8;
        uint256 k = y % 4;
        stamp = 5;
        if (pairs.length == 0) {
            pairs.push(Pair(1, 2));
            pairs.push(Pair(3, 4));
            pairs.push(Pair(5, 6));
            pairs.push(Pair(7, 8));
            pairs.push(Pair(9, 10));
        }
        // `string` mapping value: the right-hand side is built before the key.
        if (c == 0) {
            labels[y - 1] = string(abi.encodePacked(10 / y));
            out = bytes(labels[y - 1]).length;
        }
        if (c == 1) {
            labels[bump(k)] = string(abi.encodePacked(stamp + 100));
            out = uint256(keccak256(bytes(labels[k]))) % 1000;
            // An inert storage source beside a key without effects: order not observable.
            labels[k + 4] = labels[k];
        }
        // Storage struct source into a storage array element (raw-slot target): read after the
        // key helper; its own index runs before the target's.
        if (c == 2) {
            pairs[touchPairs(k + 1)] = pairs[0];
            out = pairs[k + 1].a * 1000 + pairs[k + 1].b;
            // Conditionals of references beside keys without effects.
            pairs[k] = y > 1 ? pairs[0] : pairs[1];
            held[k + 20] = y > 1 ? held[0] : held[1];
        }
        if (c == 3) {
            uint256 i = k;
            pairs[i++ % 4 + 1] = pairs[i];
            pairs[bump(k)] = pairs[stamp % 3];
            out = pairs[k].a * 1000000 + pairs[k + 1].a * 1000 + pairs[(k + 1) % 4 + 1].b;
        }
        // Storage struct source into a mapping value: its own keys run before the target's.
        if (c == 4) {
            held[0] = pairs[0];
            uint256 i = k;
            held[i++ + 4] = held[i];
            held[touchHeld(k + 8)] = held[0];
            out = held[k + 4].a * 1000000 + held[k + 8].a * 1000 + held[k + 8].b;
        }
        if (c == 5) {
            held[2] = Pair(stamp, 50);
            held[bump(k + 12)] = heldAt(stamp % 3);
            cursor = k;
            held[cursor++ + 16] = held[cursor];
            out = held[k + 12].a * 1000 + held[k + 16].b + cursor * 1000000;
        }
        // Two-key mapping value with a source key the key helper changes.
        if (c == 6) {
            grid[stamp % 3][1] = Pair(stamp, 60);
            grid[bump(k)][1] = grid[stamp % 3][1];
            out = grid[k][1].a * 1000 + grid[k][1].b;
        }
        // The source's index reverts before the target's key.
        if (c == 7) {
            pairs[y - 1] = pairs[10 / y % 5];
            held[y - 1] = held[10 / y];
            out = pairs[(y - 1) % 5].a;
        }
        emit Written(c, out);
        return out;
    }

    function fail() external {
        stamp = 123;
        require(false, "struct copy order rollback");
    }

    function read() external view returns (uint256) {
        return out + stamp;
    }
}
