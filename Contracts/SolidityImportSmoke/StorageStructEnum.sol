// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract StorageStructEnum {
    enum Mode { None, First, Second }
    struct Entry {
        uint16 left;
        Mode mode;
        uint8 right;
        mapping(address => Mode) levels;
    }
    mapping(bytes32 => Entry) internal entries;

    function mode(bytes32 id) external view returns (Mode) { return entries[id].mode; }
    function level(bytes32 id, address k) external view returns (Mode) { return entries[id].levels[k]; }
    function unused(bytes32 id, address k) external view returns (uint16) {
        Mode a = entries[id].mode;
        Mode b = entries[id].levels[k];
        return entries[id].left;
    }
    function set(bytes32 id, address k) external {
        entries[id].mode = Mode.Second;
        entries[id].levels[k] = Mode.First;
    }
    function clear(bytes32 id, address k) external {
        delete entries[id].mode;
        delete entries[id].levels[k];
    }
    function setNeighbors(bytes32 id, uint16 left, uint8 right) external {
        entries[id].left = left;
        entries[id].right = right;
    }
    function compare(bytes32 id) external view returns (bool) {
        return entries[id].mode == Mode.First;
    }
    struct Packed { uint16 left; Mode mode; uint8 right; }
    mapping(bytes32 => Packed) internal packed;
    function clearWhole(bytes32 id) external { delete packed[id]; }
    function dirtyPacked(bytes32 id, Mode x) external {
        entries[id].mode = x;
    }
    function dirtyMapped(bytes32 id, address k, Mode x) external {
        entries[id].levels[k] = x;
    }
    struct Indexed { mapping(Mode => Mode) modes; }
    mapping(bytes32 => Indexed) internal indexedEntries;
    function enumKeyedMapping(bytes32 id) external {
        indexedEntries[id].modes[Mode.None] = Mode.First;
    }
    mapping(Mode => Entry) internal byMode;
    function dirtyKey() external {
        Mode k = Mode.None;
        assembly { k := 3 }
        byMode[k].mode = Mode.First;
    }
    struct Narrow { Mode mode; mapping(uint8 => Mode) levels; mapping(uint8 => uint256) values; }
    mapping(uint256 => Narrow) internal narrow;
    function narrowKey() external returns (Mode) {
        uint8 k = 0;
        assembly { k := 257 }
        narrow[0].levels[k] = Mode.First;
        return narrow[0].levels[1];
    }
    function siblingKey() external returns (uint256) {
        uint8 k = 0;
        assembly { k := 257 }
        narrow[0].values[k] = 7;
        return narrow[0].values[1];
    }
    function writeLeaf(mapping(address => Mode) storage levels, address k) internal {
        levels[k] = Mode.First;
    }
    function helperWrite(bytes32 id, address k) external {
        writeLeaf(entries[id].levels, k);
    }
}
