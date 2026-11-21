// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Storage structs with a `string` or `bytes` member next to scalar members. The dynamic
// member owns one whole slot and is never touched here; its scalar siblings before and after
// it (including a bool packed after a narrow member) are read and written through a one-key
// mapping, a two-key mapping, a storage reference and a plain state variable, and a state
// variable declared after the three-slot struct keeps its own slot.
contract SequenceFixture {
    struct Category {
        uint128 bitmap;
        string label;
        uint64 tail;
        bool active;
    }
    struct Blob {
        uint8 flag;
        bytes data;
        uint256 count;
    }
    mapping(uint8 => Category) internal categories;
    mapping(uint256 => mapping(address => Blob)) internal blobs;
    Category internal top;
    uint256 internal last;
    function change(uint256 x) external returns (uint256) {
        uint8 id = uint8(x);
        uint8 other = uint8(x >> 1);
        uint256 outer = x % 3;
        categories[id].bitmap = uint128(x >> 8);
        Category storage c = categories[other];
        c.tail = uint64(x >> 136);
        c.active = (x & 1) == 1;
        blobs[outer][msg.sender].flag = uint8(x >> 200);
        blobs[outer][msg.sender].count += 1;
        top.bitmap = uint128(x);
        top.tail += 1;
        top.active = !top.active;
        last = x;
        uint256 acc = uint256(categories[id].bitmap) + uint256(c.tail);
        if (categories[id].active) {
            acc = acc + 1;
        }
        acc = acc + uint256(blobs[outer][msg.sender].flag) + blobs[outer][msg.sender].count;
        return acc + uint256(top.tail) + (top.active ? 2 : 0);
    }
    function fail() external {
        top.tail = type(uint64).max;
        top.tail += 1;
    }
    function read() external view returns (uint256) {
        return uint256(top.bitmap) + uint256(top.tail) + last;
    }
}
