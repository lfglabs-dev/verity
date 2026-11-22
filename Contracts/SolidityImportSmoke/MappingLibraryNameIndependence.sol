// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// An internal library function over a storage mapping is modeled by its own body, whatever the
// library and function are called. `TickBitmap.flipTick` with three arguments once selected a
// fixed bitmap XOR lowering in place of the body.

library TickBitmap {
    function flipTick(mapping(int16 => uint256) storage self, int24 tick, int24 tickSpacing) internal {
        require(tickSpacing > 0);
        self[int16(tick >> 8)] |= uint256(1) << uint8(uint24(tick) & 0xff);
    }
}

library BitmapSet {
    function setBit(mapping(int16 => uint256) storage self, int24 tick, int24 tickSpacing) internal {
        require(tickSpacing > 0);
        self[int16(tick >> 8)] |= uint256(1) << uint8(uint24(tick) & 0xff);
    }
}

// The same body under two library and function names: both must import, and agree with solc.
contract MappingLibraryNameIndependence {
    struct Pool {
        mapping(int16 => uint256) bitmap;
        uint256 liquidity;
    }

    Pool private pool;
    uint256 private count;

    function viaTickName(int24 tick, int24 spacing) external returns (uint256) {
        TickBitmap.flipTick(pool.bitmap, tick, spacing);
        return pool.bitmap[int16(tick >> 8)];
    }

    function viaOtherName(int24 tick, int24 spacing) external returns (uint256) {
        BitmapSet.setBit(pool.bitmap, tick, spacing);
        return pool.bitmap[int16(tick >> 8)];
    }
}
