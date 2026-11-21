// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A function returning bytes32[] from a (start slot, count) pair whose last statement is an
// assembly block that encodes and returns the array. The importer replaces one exact block
// (the contiguous storage read of `loadRange` below) with a fixed lowering bound to the
// variables the block references, and must reject any other block of that shape.
contract TailAssemblyRangeRead {
    uint256 private first = 7;
    uint256 private second = 9;

    function loadRange(bytes32 startSlot, uint256 nSlots) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            let length := shl(5, nSlots)
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), nSlots)
            memptr := add(memptr, 0x40)
            let end := add(memptr, length)
            for {} 1 {} {
                mstore(memptr, sload(startSlot))
                memptr := add(memptr, 0x20)
                startSlot := add(startSlot, 1)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }

    // The same block with the parameters declared in the other order: the lowering follows
    // the references, not the parameter positions.
    function loadRangeSwapped(uint256 nSlots, bytes32 startSlot) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            let length := shl(5, nSlots)
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), nSlots)
            memptr := add(memptr, 0x40)
            let end := add(memptr, length)
            for {} 1 {} {
                mstore(memptr, sload(startSlot))
                memptr := add(memptr, 0x20)
                startSlot := add(startSlot, 1)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }

    // The exact block over local variables: the lowering reads the locals the block references.
    function loadRangeFromLocals(uint256 base, uint256 count) external view returns (bytes32[] memory) {
        bytes32 startSlot = bytes32(base + 1);
        uint256 nSlots = count;
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            let length := shl(5, nSlots)
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), nSlots)
            memptr := add(memptr, 0x40)
            let end := add(memptr, length)
            for {} 1 {} {
                mstore(memptr, sload(startSlot))
                memptr := add(memptr, 0x20)
                startSlot := add(startSlot, 1)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }

    // Same shape and Yul names, but returns the slot keys: solc returns [0, 1] for (0, 2),
    // not the stored [7, 9].
    function echoRange(bytes32 startSlot, uint256 nSlots) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            let length := shl(5, nSlots)
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), nSlots)
            memptr := add(memptr, 0x40)
            let end := add(memptr, length)
            for {} 1 {} {
                mstore(memptr, startSlot)
                memptr := add(memptr, 0x20)
                startSlot := add(startSlot, 1)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }

    // The exact block with `nSlots` a narrower type: the lowering is bound to the declared
    // types it models (bytes32, uint256) and rejects this.
    function loadRangeNarrow(bytes32 startSlot, uint8 nSlots) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            let length := shl(5, nSlots)
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), nSlots)
            memptr := add(memptr, 0x40)
            let end := add(memptr, length)
            for {} 1 {} {
                mstore(memptr, sload(startSlot))
                memptr := add(memptr, 0x20)
                startSlot := add(startSlot, 1)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }
}
