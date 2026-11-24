// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Static-array members (reserved `uint256[N]` gaps, packed `uint64[N]`, nested `address[2][2]`,
// struct arrays) inside storage structs. Each static array starts a fresh slot, takes solc's
// footprint, and the next member starts a fresh slot; the array member itself stays opaque
// and only places the later members (SyntheticGapStorageChecks.lean).
contract SyntheticGapStorage {
    struct Pair {
        uint128 low;
        uint128 high;
        uint256 extra;
    }

    struct Layout {
        uint128 head;
        uint256[3] __gap;
        address admin;
        bool paused;
        uint64[5] packedGap;
        address[2][2] nestedGap;
        Pair[2] pairs;
        uint256 tail;
    }

    struct Outer {
        uint8 tag;
        Layout inner;
        uint256 after_;
    }

    bytes32 private constant LAYOUT_SLOT =
        0x5d8e1f0a7c2b3e4d5f60718293a4b5c6d7e8f9011223344556677889900aab00;
    bytes32 private constant OUTER_SLOT =
        0x6e9f20b18d3c4f5e607182a3b4c5d6e7f8091a2b3c4d5e6f708192a3b4c5d600;

    function _layout() private pure returns (Layout storage $) {
        assembly ("memory-safe") {
            $.slot := LAYOUT_SLOT
        }
    }

    function _outer() private pure returns (Outer storage $) {
        assembly ("memory-safe") {
            $.slot := OUTER_SLOT
        }
    }

    function setAll(uint128 head, address admin, bool paused, uint256 tail) external {
        Layout storage $ = _layout();
        $.head = head;
        $.admin = admin;
        $.paused = paused;
        $.tail = tail;
    }

    function getAll() external view returns (uint128, address, bool, uint256) {
        Layout storage $ = _layout();
        return ($.head, $.admin, $.paused, $.tail);
    }

    function setOuter(uint8 tag, uint256 tail, uint256 afterValue) external {
        Outer storage $ = _outer();
        $.tag = tag;
        $.inner.tail = tail;
        $.after_ = afterValue;
    }

    function getOuter() external view returns (uint8, uint256, uint256) {
        Outer storage $ = _outer();
        return ($.tag, $.inner.tail, $.after_);
    }
}

// Layout-backed structs (state variables, mapping values) with static-array members.
contract SyntheticGapStorageMapped {
    struct Record {
        uint256 first;
        address[3] gap;
        bool[5] flags;
        uint128 last;
    }

    Record private single;
    mapping(uint256 => Record) private records;

    function setRecord(uint256 k, uint256 first, uint128 last) external {
        records[k].first = first;
        records[k].last = last;
        single.last = last;
    }

    function getRecord(uint256 k) external view returns (uint256, uint128, uint128) {
        return (records[k].first, records[k].last, single.last);
    }
}

// Access to an opaque nested static-array member fails closed.
contract SyntheticGapStorageUnsupported {
    struct Layout {
        uint256 head;
        uint256[2][2] __gap;
        uint256 tail;
    }

    bytes32 private constant LAYOUT_SLOT =
        0x5d8e1f0a7c2b3e4d5f60718293a4b5c6d7e8f9011223344556677889900aab00;

    function _layout() private pure returns (Layout storage $) {
        assembly ("memory-safe") {
            $.slot := LAYOUT_SLOT
        }
    }

    function readGap(uint256 i) external view returns (uint256) {
        return _layout().__gap[i][0];
    }

    function writeGap(uint256 v) external {
        _layout().__gap[1][0] = v;
    }
}
