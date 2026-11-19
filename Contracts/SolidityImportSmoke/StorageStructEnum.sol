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
    function dirtyPacked(bytes32 id) external {
        Mode x = Mode.None;
        assembly { x := 3 }
        entries[id].mode = x;
    }
    function dirtyMapped(bytes32 id, address k) external {
        Mode x = Mode.None;
        assembly { x := 3 }
        entries[id].levels[k] = x;
    }
}
