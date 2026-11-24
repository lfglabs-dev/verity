// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IAsset {
    function decimals() external view returns (uint8);
}

interface IRegistry {
    enum Grade {
        Base,
        Plus,
        Max
    }

    struct Config {
        IAsset asset;
        Grade grade;
        uint256 weight;
    }

    struct Order {
        IAsset asset;
        uint256 amount;
        bytes payload;
    }

    struct Item {
        IAsset asset;
        uint256 qty;
    }
}

/// Synthetic fixture covering storage struct `enum` packing & `Panic(0x21)` checks,
/// `abi.decode` of nested static structs with `enum` members, and ABI schema
/// resolution of interface-declared structs with interface-typed fields.
contract EnumStructNestedDecode {
    enum Level {
        Low,
        High
    }

    struct Packed {
        uint64 head;
        Level level;
        uint64 tail;
        bool flag;
    }

    struct Outer {
        Packed inner;
        Level tag;
        uint256 rest;
    }

    Packed internal stored;
    Outer internal whole;
    Packed[] internal list;

    function writePacked(uint64 head, uint8 levelRaw, uint64 tail, bool flag) external {
        stored.head = head;
        stored.level = Level(levelRaw);
        stored.tail = tail;
        stored.flag = flag;
    }

    function writeLevelParam(Level lv) external {
        stored.level = lv;
    }

    function readLevelCast() external view returns (uint8) {
        return uint8(stored.level);
    }

    function isHigh() external view returns (bool) {
        return stored.level == Level.High;
    }

    function readUnusedLevel() external view returns (uint64) {
        Level unused = stored.level;
        return stored.head;
    }

    function copyPackedToMemory() external view returns (uint64, uint8, uint64, bool) {
        Packed memory p = stored;
        return (p.head, uint8(p.level), p.tail, p.flag);
    }

    function pushAndReadArray(uint64 head, uint8 levelRaw, uint64 tail, bool flag)
        external
        returns (uint8)
    {
        list.push();
        uint256 idx = list.length - 1;
        list[idx].head = head;
        list[idx].level = Level(levelRaw);
        list[idx].tail = tail;
        list[idx].flag = flag;
        return uint8(list[idx].level);
    }

    function decodeOuter(bytes memory data) external returns (uint256, uint8, uint8, bool) {
        Outer memory out = abi.decode(data, (Outer));
        whole = out;
        return (out.rest + out.inner.head + out.inner.tail, uint8(out.inner.level), uint8(out.tag), out.inner.flag);
    }

    function decodeOuterTuple(bytes memory data) external pure returns (uint256, uint8) {
        (Outer memory out, uint256 extra) = abi.decode(data, (Outer, uint256));
        return (out.rest + out.inner.head + extra, uint8(out.tag));
    }

    function decodeInterfaceConfig(bytes memory data)
        external
        pure
        returns (address, uint8, uint256)
    {
        IRegistry.Config memory cfg = abi.decode(data, (IRegistry.Config));
        cfg.weight += 1;
        return (address(cfg.asset), uint8(cfg.grade), cfg.weight);
    }

    function processInterfaceOrder(IRegistry.Order calldata order)
        external
        pure
        returns (address, uint256, uint256)
    {
        return (address(order.asset), order.amount, order.payload.length);
    }

    function sumInterfaceItems(IRegistry.Item[] calldata items)
        external
        pure
        returns (uint256 total, address lastAsset)
    {
        for (uint256 i = 0; i < items.length; ++i) {
            total += items[i].qty;
            lastAsset = address(items[i].asset);
        }
    }
}
