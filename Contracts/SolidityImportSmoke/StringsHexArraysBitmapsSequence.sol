// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library MathSlice39 {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + (a ^ b) / 2;
    }

    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
                result += 1;
            }
        }
        return result;
    }

    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        uint256 isGt;
        unchecked {
            isGt = value > (1 << 128) - 1 ? 1 : 0;
            value >>= isGt * 128;
            result += isGt * 16;

            isGt = value > (1 << 64) - 1 ? 1 : 0;
            value >>= isGt * 64;
            result += isGt * 8;

            isGt = value > (1 << 32) - 1 ? 1 : 0;
            value >>= isGt * 32;
            result += isGt * 4;

            isGt = value > (1 << 16) - 1 ? 1 : 0;
            value >>= isGt * 16;
            result += isGt * 2;

            result += value > (1 << 8) - 1 ? 1 : 0;
        }
        return result;
    }
}

library SignedMathSlice39 {
    function abs(int256 n) internal pure returns (uint256) {
        unchecked {
            int256 mask = n >> 255;
            return uint256((n + mask) ^ mask);
        }
    }
}

library StorageSlotSlice39 {
    struct AddressSlot {
        address value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }
}

library ArraysSlice39 {
    using StorageSlotSlice39 for bytes32;

    function findUpperBound(uint256[] storage array, uint256 element) internal view returns (uint256) {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = MathSlice39.average(low, high);
            if (unsafeAccess(array, mid).value > element) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        if (low > 0 && unsafeAccess(array, low - 1).value == element) {
            return low - 1;
        } else {
            return low;
        }
    }

    function unsafeAccess(address[] storage arr, uint256 pos) internal pure returns (StorageSlotSlice39.AddressSlot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getAddressSlot();
    }

    function unsafeAccess(uint256[] storage arr, uint256 pos) internal pure returns (StorageSlotSlice39.Uint256Slot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getUint256Slot();
    }
}

library BitMapsSlice39 {
    struct BitMap {
        mapping(uint256 bucket => uint256) _data;
    }

    function get(BitMap storage bitmap, uint256 index) internal view returns (bool) {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        return bitmap._data[bucket] & mask != 0;
    }

    function setTo(BitMap storage bitmap, uint256 index, bool value) internal {
        if (value) {
            set(bitmap, index);
        } else {
            unset(bitmap, index);
        }
    }

    function set(BitMap storage bitmap, uint256 index) internal {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        bitmap._data[bucket] |= mask;
    }

    function unset(BitMap storage bitmap, uint256 index) internal {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        bitmap._data[bucket] &= ~mask;
    }
}

library StringsSlice39 {
    bytes16 private constant HEX_DIGITS = "0123456789abcdef";
    uint8 private constant ADDRESS_LENGTH = 20;

    error StringsInsufficientHexLength(uint256 value, uint256 length);

    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = MathSlice39.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            assembly ("memory-safe") {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                assembly ("memory-safe") {
                    mstore8(ptr, byte(mod(value, 10), HEX_DIGITS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    function toStringSigned(int256 value) internal pure returns (string memory) {
        return string.concat(value < 0 ? "-" : "", toString(SignedMathSlice39.abs(value)));
    }

    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, MathSlice39.log256(value) + 1);
        }
    }

    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        uint256 localValue = value;
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = HEX_DIGITS[localValue & 0xf];
            localValue >>= 4;
        }
        if (localValue != 0) {
            revert StringsInsufficientHexLength(value, length);
        }
        return string(buffer);
    }

    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), ADDRESS_LENGTH);
    }

    function equal(string memory a, string memory b) internal pure returns (bool) {
        return bytes(a).length == bytes(b).length && keccak256(bytes(a)) == keccak256(bytes(b));
    }

    function nibbleCode(uint256 idx) internal pure returns (uint8) {
        return uint8(HEX_DIGITS[idx & 0x0f]) ^ uint8(bytes1(":"));
    }
}

contract SequenceFixture {
    using ArraysSlice39 for uint256[];
    using ArraysSlice39 for address[];
    using BitMapsSlice39 for BitMapsSlice39.BitMap;
    using StringsSlice39 for uint256;
    using StringsSlice39 for int256;
    using StringsSlice39 for address;

    event HexSnapshotRecorded(address indexed actor, uint256 indexed upperIdx, bytes32 hexDigest, bool bitEnabled);

    uint256[] private _checkpoints;
    address[] private _signers;
    BitMapsSlice39.BitMap private _bitmap;
    mapping(address account => string) private _hexLabels;

    uint256 private totalDigestScore;
    bytes32 private rollingDigest;

    function formatHex(uint256 value) public pure returns (string memory) {
        return value.toHexString();
    }

    function formatHexFixed(uint256 value, uint256 length) public pure returns (string memory) {
        return value.toHexString(length);
    }

    function formatAddressHex(address account) public pure returns (string memory) {
        return account.toHexString();
    }

    function formatSignedDecimal(int256 value) public pure returns (string memory) {
        return value.toStringSigned();
    }

    function checkStringEqual(string memory a, string memory b) public pure returns (bool) {
        return StringsSlice39.equal(a, b);
    }

    function upperBound(uint256 element) public view returns (uint256) {
        return _checkpoints.findUpperBound(element);
    }

    function bitmapBit(uint256 index) public view returns (bool) {
        return _bitmap.get(index);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 step = (input & 0x0f) + 1;
        uint256 len = _checkpoints.length;
        uint256 nextCheckpoint = len == 0 ? step * 10 : ArraysSlice39.unsafeAccess(_checkpoints, len - 1).value + step * 10;
        _checkpoints.push(nextCheckpoint);
        _signers.push(msg.sender);

        if (_checkpoints.length > 1 && (input & 1) == 1) {
            uint256 lastIdx = _checkpoints.length - 1;
            ArraysSlice39.unsafeAccess(_checkpoints, lastIdx).value = nextCheckpoint + 3;
            ArraysSlice39.unsafeAccess(_signers, lastIdx).value = address(uint160(uint256(uint160(msg.sender)) ^ 1));
        }

        uint256 bitIdx = input & 0x1ff;
        bool enableBit = (input & 2) == 0;
        _bitmap.setTo(bitIdx, enableBit);

        uint256 queryTarget = nextCheckpoint - (input & 7);
        uint256 ub = _checkpoints.findUpperBound(queryTarget);

        string memory hexAuto = ((input & 0xffff) + 1).toHexString();
        string memory hexFixed = (input & 0xfff).toHexString(2);
        string memory addrHex = ArraysSlice39.unsafeAccess(_signers, _signers.length - 1).value.toHexString();
        int256 signedVal = (input & 4) == 0 ? -int256((input & 0xff) + 1) : int256((input & 0xff) + 1);
        string memory signedStr = signedVal.toStringSigned();

        string memory combined = string.concat(hexAuto, ":", hexFixed, ":", signedStr);
        _hexLabels[msg.sender] = combined;
        bool sameLabel = StringsSlice39.equal(_hexLabels[msg.sender], combined);
        uint8 nibXor = StringsSlice39.nibbleCode(input);

        bytes32 digest = keccak256(bytes(string.concat(combined, ":", addrHex)));
        bool bitNow = _bitmap.get(bitIdx);

        emit HexSnapshotRecorded(msg.sender, ub, digest, bitNow);

        uint256 delta;
        unchecked {
            delta =
                (uint256(digest) & 0xffffffff) +
                ub * 1000 +
                (bitNow ? 500 : 100) +
                (sameLabel ? 77 : 0) +
                uint256(nibXor) +
                bytes(_hexLabels[msg.sender]).length;
            totalDigestScore += delta;
        }
        rollingDigest = rollingDigest ^ digest ^ bytes32(ub);
        require(input != 20, "SHAB: rollback");
        return totalDigestScore;
    }

    function fail() external {
        _bitmap.setTo(7, true);
        totalDigestScore += 999;
        revert("SHAB: fail");
    }

    function read() external view returns (uint256, bytes32, uint256, bool) {
        return (
            totalDigestScore,
            rollingDigest,
            _checkpoints.length,
            _bitmap.get(0)
        );
    }
}
