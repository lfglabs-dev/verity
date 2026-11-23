// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// An internal library function bound with `using ... for` to a one-key mapping state variable of
// structs, returning a storage pointer to the entry after a `require` with a custom error
// (`entries.get(k)`). solc (legacy and via-IR) reverts with the exact custom-error payload on a
// missing key, and the returned pointer is the entry itself: writes and reads through it hit
// the same slots as `entries[k].field`, packed and nested members included, and a second
// pointer to the same entry aliases the first. x = 32 * v + 8 * k + c runs case c on key k
// with value v; key 0 is never listed. Keys with side effects (`get(bump(k))`, `get(i++)`), a
// member write on the call result (`get(k).a = v`) and a named result assigned before further
// statements are located rejections (`storage-pointer-mapping-helper-*-rejected`).
struct Inner {
    uint64 x;
    uint64 y;
}

struct Entry {
    address owner;
    uint16 a;
    uint8 b;
    Inner inner;
    uint256 big;
}

error EntryMissing();
error EntryKeyMissing(uint256 key);

library EntryLookup {
    function get(mapping(uint256 => Entry) storage entries, uint256 key)
        internal view returns (Entry storage)
    {
        Entry storage entry = entries[key];
        require(entry.owner != address(0), EntryMissing());
        return entry;
    }

    // A custom error with an argument.
    function getChecked(mapping(uint256 => Entry) storage entries, uint256 key)
        internal view returns (Entry storage)
    {
        Entry storage entry = entries[key];
        require(entry.owner != address(0), EntryKeyMissing(key));
        return entry;
    }

    // The mapping parameter forwarded to another library function.
    function forward(mapping(uint256 => Entry) storage entries, uint256 key)
        internal view returns (Entry storage)
    {
        return get(entries, key);
    }
}

contract SequenceFixture {
    using EntryLookup for mapping(uint256 => Entry);

    mapping(uint256 => Entry) internal entries;
    uint256 internal stamp;

    event Touched(uint256 selector, uint256 stamp);

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 8;
        uint256 k = (x / 8) % 4;
        uint256 v = x / 32;
        if (c == 0) {
            if (k != 0) { entries[k].owner = address(uint160(0x1000 + k)); }
        }
        if (c == 1) {
            // Writes through the pointer, then a second pointer to the same entry.
            Entry storage e = entries.get(k);
            e.a = uint16(v);
            e.b = uint8(v >> 16);
            e.inner.y = uint64(v >> 24);
            e.big = v;
            Entry storage f = entries.get(k);
            f.inner.x = f.inner.y + 1;
        }
        if (c == 2) {
            Entry storage e = entries.getChecked(k);
            e.big += 1;
        }
        if (c == 3) {
            // A pointer through a computed key, then a member read on the call result.
            Entry storage e = entries.get((k * 5) % 4);
            e.a = uint16(v + 1);
            stamp = entries.get(k).a;
        }
        if (c == 4) {
            Entry storage e = entries.forward(k);
            stamp = e.big + e.a + e.b + e.inner.x + e.inner.y;
        }
        if (c == 5) {
            delete entries[k];
        }
        if (c == 6) {
            // Reads through the pointer match direct reads of the same entry.
            Entry storage e = entries.get(k);
            stamp = (e.inner.x == entries[k].inner.x && e.a == entries[k].a) ? 1 : 2;
        }
        if (c == 7) {
            // A write directly to the entry is seen through an earlier pointer.
            Entry storage e = entries.get(k);
            entries[k].b = uint8(v);
            stamp = e.b;
        }
        emit Touched(c, stamp);
        return stamp;
    }

    function fail() external {
        stamp = 123;
        Entry storage e = entries.get(1);
        e.big = 7;
        revert("storage pointer helper rollback");
    }

    function fold(uint256 acc, uint256 k) internal view returns (uint256) {
        Entry storage e = entries[k];
        unchecked {
            acc = acc * 31 + uint160(e.owner);
            acc = acc * 31 + e.a;
            acc = acc * 31 + e.b;
            acc = acc * 31 + e.inner.x;
            acc = acc * 31 + e.inner.y;
            acc = acc * 31 + e.big;
        }
        return acc;
    }

    function read() external view returns (uint256) {
        uint256 acc;
        unchecked {
            acc = stamp * 31 + 1;
        }
        acc = fold(acc, 0);
        acc = fold(acc, 1);
        acc = fold(acc, 2);
        acc = fold(acc, 3);
        return acc;
    }
}
