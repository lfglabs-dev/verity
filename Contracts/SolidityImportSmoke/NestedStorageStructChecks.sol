// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Single-state-variable contract exercising nested sub-struct whole-struct assignment (#2729)
// and flat memory struct return (#2730), independent of state variable count.
contract NestedStorageStructSingleVar {
    struct Part {
        uint128 low;
        bool enabled;
        uint64 high;
        uint256 full;
    }

    struct Record {
        uint256 beforeSlot;
        Part part;
        uint256 afterSlot;
        uint256[] extra;
    }

    mapping(address => Record) private records;

    function fromMemory(address k, Part memory p) external {
        records[k].part = p;
    }

    function fromCalldata(address k, Part calldata p) external {
        records[k].part = p;
    }

    function readPart(address k) external view returns (Part memory) {
        return records[k].part;
    }
}

// Unsupported nested storage sub-struct shapes that fail closed with located diagnostics.
contract NestedStorageStructUnsupported {
    struct DynamicPart {
        uint128 low;
        uint256[] extra;
    }

    struct FixedArrayPart {
        uint128 low;
        uint128[2] bands;
    }

    struct Leaf {
        uint128 a;
    }

    struct NestedPart {
        Leaf leaf;
        uint128 b;
    }

    struct OpaquePart {
        uint128 low;
        bytes[] blobs;
    }

    struct ScalarPart {
        uint128 low;
        uint128 high;
    }

    struct Holder {
        DynamicPart dynPart;
        FixedArrayPart fixedPart;
        NestedPart nestedPart;
        OpaquePart opaquePart;
        ScalarPart scalarPart;
    }

    mapping(address => Holder) private holders;

    function assignDynamicSubStruct(address k, DynamicPart calldata p) external {
        holders[k].dynPart = p;
    }

    function assignOpaqueSubStruct(address k, uint128 x) external {
        holders[k].opaquePart = OpaquePart(x, new bytes[](0));
    }

    function assignNestedSubStruct(address k, uint128 x) external {
        holders[k].nestedPart = NestedPart(Leaf(x), x);
    }

    function returnDynamicSubStruct(address k) external view returns (DynamicPart memory) {
        return holders[k].dynPart;
    }

    function readFixedArraySubStruct(address k) external view returns (uint128) {
        FixedArrayPart memory copy = holders[k].fixedPart;
        return copy.low;
    }

    function assignStorageToStorageSubStruct(address a, address b) external {
        holders[a].scalarPart = holders[b].scalarPart;
    }

    function deleteSubStruct(address k) external {
        delete holders[k].scalarPart;
    }

    function returnSubStructStoragePtr(address k) internal view returns (ScalarPart storage) {
        return holders[k].scalarPart;
    }
}
