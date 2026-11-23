// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Fixed-size array members of an ERC-7201 namespaced storage struct: narrow elements packed
/// several per word after a packed scalar, a bitmap-like `uint256[N]` in a nested struct read
/// and written at computed word and bit indices, an array too large to lay out slot by slot,
/// and a never-accessed reserved array between packed siblings of a mapped struct.
/// `change(x)` selects one access by `x % 8`; `y = x >> 3` gives the index in its low byte and
/// the value above it. An index past the length raises Panic(0x32), a checked narrow
/// increment past its range Panic(0x11).
contract SequenceFixture {
    struct Words {
        uint256[8] data;
    }

    struct Entry {
        address owner;
        uint8 limit;
        uint256[4] reserved;
        uint64 tail;
    }

    /// @custom:storage-location erc7201:fixture.storage.FixedArrayMembers
    struct FixedArrayStorage {
        uint64 head;
        uint8[40] small;
        bool[3] flags;
        address[2] owners;
        uint128 counter;
        Words words;
        mapping(uint256 => Entry) entries;
        uint256[600000000] wide;
        uint32 tail;
    }

    // keccak256(abi.encode(uint256(keccak256("fixture.storage.FixedArrayMembers")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant LOCATION = 0xbc52af5fc353e2311f5e35e9e951073531d069e2b2ec10e254e46ebfc238d100;

    function _storage() private pure returns (FixedArrayStorage storage $) {
        assembly {
            $.slot := LOCATION
        }
    }

    function change(uint256 x) external returns (uint256) {
        FixedArrayStorage storage $ = _storage();
        uint256 c = x % 8;
        uint256 y = x >> 3;
        uint256 lo = y & 0xff;
        if (c == 0) {
            // Lanes 32..39 are in the second word; 40..43 are out of range.
            $.small[lo % 44] = uint8(y >> 8);
            $.head = uint64(y);
            return $.small[lo % 44];
        } else if (c == 1) {
            $.small[lo % 40] += uint8(y >> 8);
            ++$.small[(y >> 16) % 40];
            return $.small[lo % 40];
        } else if (c == 2) {
            // Index 3 is out of range.
            $.flags[lo % 4] = (y >> 8) & 1 == 1;
            return $.flags[lo % 3] ? 1 : 0;
        } else if (c == 3) {
            $.owners[lo % 2] = address(uint160(y >> 8));
            $.counter += 1;
            return uint160($.owners[(lo + 1) % 2]);
        } else if (c == 4) {
            // Word 8 is out of range.
            uint256 w = (y >> 8) % 9;
            $.words.data[w] |= 1 << (y & 0xff);
            return $.words.data[w];
        } else if (c == 5) {
            Words storage words = $.words;
            uint256 w = (y >> 8) % 8;
            words.data[w] &= ~(1 << (y & 0xff));
            delete $.small[lo % 40];
            return (words.data[w] >> (y & 0xff)) & 1;
        } else if (c == 6) {
            uint256 i = y > 1 << 252 ? y : y % 600000002;
            $.wide[i] = y;
            $.tail = uint32(y);
            return $.wide[i] ^ $.wide.length;
        } else {
            Entry storage e = $.entries[y % 4];
            e.owner = msg.sender;
            e.limit = uint8(y);
            e.tail = uint64(y >> 8);
            return e.limit + e.tail + $.small.length;
        }
    }

    function fail() external view {
        require(_storage().counter <= 15, "range");
    }

    function read() external view returns (uint256) {
        FixedArrayStorage storage $ = _storage();
        uint256 acc = $.head + $.counter + $.tail;
        acc += uint256($.small[0]) + uint256($.small[31]) * 3 + uint256($.small[32]) * 5 + uint256($.small[39]) * 7;
        acc += ($.flags[0] ? 1 : 0) + ($.flags[2] ? 2 : 0) + $.entries[1].limit + $.entries[1].tail;
        acc ^= uint160($.owners[1]);
        acc ^= $.words.data[0] ^ $.words.data[7] ^ $.wide[599999999] ^ $.wide[0];
        return acc;
    }
}
