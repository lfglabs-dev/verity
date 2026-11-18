// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Root `S[] calldata` / `S[] memory` parameters of a flat scalar struct
// (#2708): the array is member `w` of the root argument tuple, so it is
// decoded with solc's eager array-head checks (calldata) or eager copy
// (memory), and read like a struct-array member of an ABI struct. A memory
// array allocates only itself and its elements, exactly as solc does.
contract SequenceFixture {
    struct Item {
        address target;
        uint256 value;
    }

    struct Packed {
        uint64 amount;
        bool active;
        uint8 tag;
    }

    uint256 private stored;

    // The issue's shape.
    function processBatch(Item[] calldata items) external pure returns (uint256) {
        return items.length;
    }

    function sumCalldata(Item[] calldata items) external pure returns (uint256 total) {
        for (uint256 i = 0; i < items.length; i++) {
            total += items[i].value;
        }
    }

    function sumMemory(Item[] memory items) external pure returns (uint256 total) {
        for (uint256 i = 0; i < items.length; i++) {
            total += items[i].value;
        }
    }

    function targetAt(Item[] calldata items, uint256 i) external pure returns (address) {
        return items[i].target;
    }

    function targetAtMemory(Item[] memory items, uint256 i) external pure returns (address) {
        return items[i].target;
    }

    // The array behind scalar, `bytes` and `T[N]` head words: its head word is 4.
    function afterHead(uint256 a, bytes calldata b, uint256[2] memory c, Packed[] calldata items)
        external
        pure
        returns (uint256 acc)
    {
        acc = a + b.length + c[1] + items.length;
        for (uint256 i = 0; i < items.length; i++) {
            if (items[i].active) acc += items[i].amount + items[i].tag;
        }
    }

    function afterHeadMemory(uint256 a, Packed[] memory items, uint256 z) external returns (uint256) {
        uint256 acc = a + z;
        for (uint256 i = 0; i < items.length; i++) {
            if (items[i].active) acc += items[i].amount * items[i].tag;
        }
        stored = acc;
        return items.length;
    }

    // Two arrays: two independent head words.
    function pairSum(Item[] calldata xs, Item[] memory ys) external pure returns (uint256) {
        uint256 total = xs.length * 1000 + ys.length;
        if (xs.length > 0 && ys.length > 0) total += xs[0].value + ys[ys.length - 1].value;
        return total;
    }

    // `items[i]` bound to a struct local (calldata, memory, calldata copied
    // to memory) and passed to a helper.
    function elementCalldata(Item[] calldata items, uint256 i) external pure returns (uint256) {
        Item calldata it = items[i];
        return it.value ^ uint256(uint160(it.target));
    }

    function elementMemory(Item[] memory items, uint256 i) external pure returns (uint256) {
        Item memory it = items[i];
        return it.value ^ uint256(uint160(it.target));
    }

    function elementCopied(Item[] calldata items, uint256 i) external pure returns (uint256) {
        Item memory it = items[i];
        return it.value ^ uint256(uint160(it.target));
    }

    function elementHelper(Item[] calldata items, uint256 i) external pure returns (uint256) {
        return valueOf(items[i]);
    }

    function valueOf(Item calldata it) internal pure returns (uint256) {
        return it.value + 1;
    }

    function change(uint256 x) external {
        stored = x;
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
