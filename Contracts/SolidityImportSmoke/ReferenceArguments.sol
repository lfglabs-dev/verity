pragma solidity 0.8.34;

struct ReferenceBox { uint128[] values; uint256 tag; }
struct StaticReferenceBox { uint128 value; uint256 tag; }

library ReferenceReaders {
    function first(ReferenceBox memory box) internal pure returns (uint256) {
        return box.values[0];
    }
}

contract ReferenceArguments {
    using ReferenceReaders for ReferenceBox;
    uint256 public stored;
    event Read(uint256 indexed tag, uint256 value);

    function memoryRead(ReferenceBox memory box) external returns (uint256) {
        uint256 value = nested(box);
        stored = value;
        emit Read(box.tag, value);
        return value;
    }
    function calldataRead(ReferenceBox calldata box) external returns (uint256) {
        uint256 value = readCalldata(box);
        stored = value;
        emit Read(box.tag, value);
        return value;
    }
    function rightRoot(ReferenceBox memory left, ReferenceBox memory right)
        external pure returns (uint256) {
        uint256 before = nested(left);
        uint256 selected = nested(right);
        return before + selected + left.tag;
    }
    function sameRoot(ReferenceBox memory box) external pure returns (uint256) {
        return twoRoots(box, box);
    }
    function usingReceiver(ReferenceBox memory box) external pure returns (uint256) {
        return box.first();
    }
    function staticRead(StaticReferenceBox memory box) external pure returns (uint256) {
        return readStatic(box);
    }
    function guarded(ReferenceBox calldata box, uint256 flag) external pure returns (uint256) {
        return guardedRead(box, flag);
    }
    function nested(ReferenceBox memory box) internal pure returns (uint256) {
        return ReferenceReaders.first(box);
    }
    function readCalldata(ReferenceBox calldata box) internal pure returns (uint256) {
        return box.values[0];
    }
    function twoRoots(ReferenceBox memory left, ReferenceBox memory right)
        internal pure returns (uint256) {
        return left.values[0] + right.tag;
    }
    function readStatic(StaticReferenceBox memory box) internal pure returns (uint256) {
        return box.value + box.tag;
    }
    function guardedRead(ReferenceBox calldata box, uint256 flag) internal pure returns (uint256) {
        require(flag != 0, "first");
        return box.values[0];
    }
    function read() external view returns (uint256) { return stored; }
}
