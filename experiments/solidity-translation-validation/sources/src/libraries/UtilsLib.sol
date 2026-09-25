// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (c) 2026 Morpho Association
pragma solidity ^0.8.0;

library UtilsLib {
    error CastOverflow();

    /// @dev Returns min(a, b).
    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := xor(x, mul(xor(x, y), lt(y, x)))
        }
    }

    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
        }
    }

    /// @dev Returns (x * y) / d rounded down.
    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    /// @dev Returns (x * y) / d rounded up.
    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    function toUint128(uint256 x) internal pure returns (uint128) {
        require(x <= type(uint128).max, CastOverflow());
        // forge-lint: disable-next-item(unsafe-typecast) as x is less than type(uint128).max
        return uint128(x);
    }

    function countBits(uint128 x) internal pure returns (uint256) {
        unchecked {
            x = x - ((x >> 1) & 0x55555555555555555555555555555555);
            x = (x & 0x33333333333333333333333333333333) + ((x >> 2) & 0x33333333333333333333333333333333);
            x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f;
            return (x * 0x01010101010101010101010101010101) >> 120;
        }
    }

    /// @dev Assumes bitmap is not zero.
    function msb(uint128 bitmap) internal pure returns (uint256 res) {
        assembly {
            res := sub(255, clz(bitmap))
        }
    }

    /// @dev Assumes bit is less than 128.
    function setBit(uint128 bitmap, uint256 bit) internal pure returns (uint128) {
        // forge-lint: disable-next-item(unsafe-typecast) as bit < 128
        return uint128(bitmap | (1 << bit));
    }

    /// @dev Assumes bit is less than 128.
    function clearBit(uint128 bitmap, uint256 bit) internal pure returns (uint128) {
        // forge-lint: disable-next-item(unsafe-typecast)
        return uint128(bitmap & ~(1 << bit));
    }

    /// @dev Sets a boolean in transient storage keyed by a (bytes32, address) pair.
    /// @dev Returns the previous value at the written slot.
    function tExchange(uint256 baseSlot, bytes32 key1, address key2, bool value) internal returns (bool previous) {
        uint256 slot = uint256(keccak256(abi.encode(key1, key2, baseSlot)));
        assembly ("memory-safe") {
            previous := tload(slot)
            tstore(slot, value)
        }
    }

    /// @dev Gets a boolean from transient storage keyed by a (bytes32, address) pair.
    function tGet(uint256 baseSlot, bytes32 key1, address key2) internal view returns (bool value) {
        uint256 slot = uint256(keccak256(abi.encode(key1, key2, baseSlot)));
        assembly ("memory-safe") {
            value := tload(slot)
        }
    }
}
