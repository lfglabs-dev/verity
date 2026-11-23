// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library StorageSlot {
    struct Uint256Slot {
        uint256 value;
    }

    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }
}

// solc (legacy and via-IR) evaluates the arguments of `bytes.concat`, `string.concat`,
// `abi.encodePacked` and `abi.encode` left to right, and reads a storage `bytes` / `string`
// argument only while encoding, after every argument has run. change(x) selects one case by
// x % 8 and drives it with y = x / 8: y = 0 makes two arguments revert (`10 / y`, `y - 1`), so
// the panic code shows which ran first; `stampOne` / `stampTwo` are helpers that write the stamp;
// `rewriteBlob` writes the storage `bytes` an earlier argument names; `moveCursor` moves the key
// of an earlier keyed storage `string` argument; a raw slot write
// (`corrupt`) gives a storage `bytes` / `string` the invalid encoding 3 (long flag, length 1),
// whose read panics with 0x22.
contract SequenceFixture {
    bytes internal blob;
    string internal label;
    uint256 internal stamp;
    uint256 internal out;
    uint256 internal cursor;
    mapping(uint256 => string) internal names;

    bytes32 internal constant BLOB_SLOT = bytes32(uint256(0));
    bytes32 internal constant LABEL_SLOT = bytes32(uint256(1));

    event Written(uint256 selector, uint256 out);

    function stampOne() internal returns (bytes memory) {
        stamp = stamp * 10 + 1;
        return abi.encodePacked(uint8(stamp));
    }

    function stampTwo() internal returns (bytes memory) {
        stamp = stamp * 10 + 2;
        return abi.encodePacked(uint8(stamp));
    }

    function rewriteBlob(uint256 y) internal returns (bytes memory) {
        blob = abi.encodePacked(y, uint8(7));
        return hex"0f";
    }

    function moveCursor() internal returns (string memory) {
        cursor = cursor + 1;
        names[cursor] = "zzz";
        return "m";
    }

    function corrupt(bytes32 slot, bool invalid) internal {
        StorageSlot.getUint256Slot(slot).value = invalid ? 3 : 0;
    }

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 8;
        uint256 y = x / 8;
        // Concat arguments: the left one's panic comes first.
        if (c == 0) {
            out = bytes.concat(abi.encodePacked(10 / y), abi.encodePacked(y - 1)).length;
        }
        if (c == 1) {
            out = bytes(string.concat(string(abi.encodePacked(10 / y)), string(abi.encodePacked(y - 1)))).length;
        }
        // Concat arguments with state writes run in source order.
        if (c == 2) {
            stamp = y % 5;
            bytes32 h = keccak256(bytes.concat(stampOne(), stampTwo()));
            out = stamp * 1000 + uint256(h) % 1000;
        }
        // A storage `bytes` concat argument is read after a later argument rewrote it.
        if (c == 3) {
            corrupt(BLOB_SLOT, false);
            blob = "ab";
            uint256 n = bytes.concat(blob, rewriteBlob(y)).length;
            out = n * 1000 + uint256(keccak256(blob)) % 1000;
            // A keyed storage `string`: its key is evaluated at its position, before a later
            // argument moves the key.
            cursor = y % 3;
            names[cursor] = "k";
            uint256 m = bytes(string.concat(names[cursor], moveCursor())).length;
            out = out * 100 + m;
        }
        // A corrupt storage `bytes` beside a later panic: the panic comes first (y = 0).
        if (c == 4) {
            corrupt(BLOB_SLOT, y % 2 == 0);
            out = bytes.concat(blob, abi.encodePacked(10 / y)).length;
        }
        if (c == 5) {
            corrupt(BLOB_SLOT, y % 2 == 0);
            out = abi.encodePacked(blob, 10 / y).length;
        }
        // `abi.encode` with a corrupt storage `string` beside a later overflow (y = 0).
        if (c == 6) {
            corrupt(LABEL_SLOT, y % 2 == 0);
            uint256 top = type(uint256).max;
            out = uint256(keccak256(abi.encode(label, (top - y) + 1))) % 1000;
        }
        // Valid storage arguments beside pure siblings keep their values.
        if (c == 7) {
            corrupt(BLOB_SLOT, false);
            corrupt(LABEL_SLOT, false);
            blob = abi.encodePacked(y, "tail");
            label = "lbl";
            out = uint256(keccak256(bytes.concat(blob, bytes32(y), blob))) % 1000 +
                uint256(keccak256(abi.encode(label, y, blob))) % 1000 * 1000;
        }
        emit Written(c, out);
        return out;
    }

    function fail() external {
        stamp = 123;
        require(false, "encoding order rollback");
    }

    function read() external view returns (uint256) {
        return out + stamp;
    }
}
