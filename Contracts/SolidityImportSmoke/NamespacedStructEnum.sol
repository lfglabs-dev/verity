// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Enum members of an ERC-7201 namespaced storage struct, observed on dirty storage words
/// (`NamespacedStructEnumChecks`), and the uses that stay outside the slice.
contract NamespacedStructEnum {
    enum Mode { None, First, Second }

    struct Entry {
        uint128 amount;
        Mode mode;
        uint8 flag;
    }

    /// @custom:storage-location erc7201:fixture.storage.EnumChecks
    struct EnumStorage {
        uint64 head;
        Mode mode;
        uint16 tail;
        mapping(uint256 => Entry) entries;
    }

    // keccak256(abi.encode(uint256(keccak256("fixture.storage.EnumChecks")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant LOCATION = 0x5d137fa045f8e23ba9b67ac5983f40ee54e497f58d893afb34609c91a4384800;

    function _storage() private pure returns (EnumStorage storage $) {
        assembly {
            $.slot := LOCATION
        }
    }

    function mode() external view returns (Mode) { return _storage().mode; }
    function entryMode(uint256 k) external view returns (Mode) { return _storage().entries[k].mode; }
    function unused(uint256 k) external view returns (uint256) {
        Mode a = _storage().mode;
        Mode b = _storage().entries[k].mode;
        return _storage().tail + _storage().entries[k].flag;
    }
    function set(uint256 k) external {
        _storage().mode = Mode.Second;
        _storage().entries[k].mode = Mode.First;
    }
    function clear(uint256 k) external {
        delete _storage().mode;
        delete _storage().entries[k].mode;
    }
    function setNeighbors(uint256 k, uint16 tail, uint8 flag) external {
        _storage().tail = tail;
        _storage().entries[k].flag = flag;
    }

    function compare() external view returns (bool) { return _storage().mode == Mode.First; }
    function convert() external view returns (uint256) { return uint256(_storage().mode); }
    function assignParam(Mode x) external { _storage().mode = x; }
    function pair() private pure returns (Mode, uint16) { return (Mode.First, 1); }
    function assignTuple() external { (_storage().mode, _storage().tail) = pair(); }
    function copyEntry(uint256 k) external view returns (uint256) {
        Entry memory e = _storage().entries[k];
        return e.amount;
    }
    function take(Entry memory e) private pure returns (uint256) { return e.amount; }
    function passEntry(uint256 k) external view returns (uint256) { return take(_storage().entries[k]); }
    function deleteEntry(uint256 k) external { delete _storage().entries[k]; }
}
