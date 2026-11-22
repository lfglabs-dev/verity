// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A library function that flips one bit of a storage bitmap in inline assembly, reverting with
// an ABI-encoded custom error built at the free-memory pointer when the position is misaligned.
// It is lowered through its body like any other library function.

library TickBitmap {
    function flipTick(mapping(int16 => uint256) storage self, int24 tick, int24 tickSpacing) internal {
        assembly ("memory-safe") {
            tick := signextend(2, tick)
            tickSpacing := signextend(2, tickSpacing)
            if smod(tick, tickSpacing) {
                let fmp := mload(0x40)
                mstore(fmp, 0xd4d8f3e6)
                mstore(add(fmp, 0x20), tick)
                mstore(add(fmp, 0x40), tickSpacing)
                revert(add(fmp, 0x1c), 0x44)
            }
            tick := sdiv(tick, tickSpacing)
            mstore(0, sar(8, tick))
            mstore(0x20, self.slot)
            let slot := keccak256(0, 0x40)
            sstore(slot, xor(sload(slot), shl(and(tick, 0xff), 1)))
        }
    }
}

contract MappingLibraryAssemblyFlip {
    struct Pool {
        mapping(int16 => uint256) bitmap;
        uint256 liquidity;
    }

    Pool private pool;
    uint256 private count;

    function flip(int24 tick, int24 spacing) external {
        TickBitmap.flipTick(pool.bitmap, tick, spacing);
    }
}
