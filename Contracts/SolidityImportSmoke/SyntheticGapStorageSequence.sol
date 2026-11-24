// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// A namespaced (raw-slot) storage struct with static-array members (a `uint256[3]` gap, a
// packed `uint64[5]`, a nested `address[2][2]`, a struct array), and a struct nesting it: each
// write lands in solc's slot, which a raw `sload` reads back.
contract SequenceFixture {
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

    uint256 private total;

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

    function change(uint256 x) external returns (uint256) {
        Layout storage $ = _layout();
        $.head = uint128(x);
        $.admin = address(uint160(x >> 8));
        $.paused = x % 2 == 1;
        $.tail = $.tail + x % 1000;
        Outer storage o = _outer();
        o.tag = uint8(x);
        o.inner.tail = x % 999;
        o.after_ = o.after_ + 1;
        uint256 tailWord;
        uint256 afterWord;
        assembly ("memory-safe") {
            tailWord := sload(add(LAYOUT_SLOT, 15))
            afterWord := sload(add(OUTER_SLOT, 17))
        }
        total = total + tailWord % 1000 + afterWord + (($.paused ? 1 : 0) << 1) + o.inner.tail;
        return total;
    }

    // The stateful harness's reverting call: its write is rolled back.
    function fail() external {
        total = total + 1;
        revert();
    }

    function read() external view returns (uint256) {
        return total;
    }
}
