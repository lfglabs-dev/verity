// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Enum members of an ERC-7201 namespaced storage struct, packed as `uint8` ordinals between
/// narrow siblings: in the namespaced struct itself, in the struct value of a mapping member
/// (through a storage pointer) and in a nested struct. Each is written from enum literals,
/// deleted, returned directly (solc's range check on the ABI result) and read into an unused
/// local, while its siblings are written and read around it. `change(x)` selects one access
/// by `x % 8`; `y = x >> 3` supplies the key and the sibling values. A sibling increment past
/// its range raises Panic(0x11).
contract SequenceFixture {
    enum Mode { Idle, Active, Paused, Closed }

    struct Entry {
        uint128 amount;
        Mode mode;
        uint8 flag;
    }

    struct Inner {
        Mode mode;
        uint240 rest;
    }

    /// @custom:storage-location erc7201:fixture.storage.EnumMembers
    struct EnumStorage {
        uint64 head;
        Mode mode;
        uint16 tail;
        mapping(uint256 => Entry) entries;
        Inner inner;
        uint256 counter;
    }

    // keccak256(abi.encode(uint256(keccak256("fixture.storage.EnumMembers")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant LOCATION = 0x9798406273bf54545c8c7b36917275d9af24fc35223b08da997dfc874f95b100;

    function _storage() private pure returns (EnumStorage storage $) {
        assembly {
            $.slot := LOCATION
        }
    }

    function change(uint256 x) external returns (Mode) {
        EnumStorage storage $ = _storage();
        uint256 c = x % 8;
        uint256 y = x >> 3;
        if (c == 0) {
            $.mode = Mode.Active;
            $.head = uint64(y);
            return $.mode;
        } else if (c == 1) {
            $.tail = uint16(y);
            $.mode = Mode.Closed;
            return $.mode;
        } else if (c == 2) {
            delete $.mode;
            $.counter += 1;
            return $.mode;
        } else if (c == 3) {
            Entry storage e = $.entries[y % 4];
            e.amount = uint128(y);
            e.mode = Mode.Paused;
            e.flag = uint8(y >> 8);
            return e.mode;
        } else if (c == 4) {
            delete $.entries[y % 4].mode;
            $.entries[y % 4].flag += 1;
            return $.entries[y % 4].mode;
        } else if (c == 5) {
            $.inner.mode = Mode.Active;
            $.inner.rest = uint240(y);
            return $.inner.mode;
        } else if (c == 6) {
            Mode before = $.entries[y % 4].mode;
            $.entries[y % 4].mode = Mode.Closed;
            return $.entries[(y >> 2) % 4].mode;
        } else {
            $.inner.rest = uint240(y);
            delete $.inner.mode;
            return $.inner.mode;
        }
    }

    function fail() external view {
        require(_storage().counter <= 3, "range");
    }

    function read() external view returns (uint256) {
        EnumStorage storage $ = _storage();
        uint256 acc = $.head + $.tail + $.counter + $.inner.rest;
        acc += $.entries[1].amount + $.entries[1].flag + $.entries[2].flag * 3;
        return acc;
    }
}
