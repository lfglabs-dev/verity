// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A function returning bytes32[] whose last statement is an assembly block that encodes and
// returns the array itself. The importer replaces two exact blocks (the storage and transient
// batch reads of `loadSlots` / `loadTransientSlots` below) with a fixed lowering, and must
// reject any other block of the same shape instead of giving it that lowering.
contract TailAssemblyArrayRead {
    uint256 private first = 7;
    uint256 private second = 9;

    function loadSlots(bytes32[] calldata slots) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), slots.length)
            memptr := add(memptr, 0x40)
            let end := add(memptr, shl(5, slots.length))
            let calldataptr := slots.offset
            for {} 1 {} {
                mstore(memptr, sload(calldataload(calldataptr)))
                memptr := add(memptr, 0x20)
                calldataptr := add(calldataptr, 0x20)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }

    function loadTransientSlots(bytes32[] calldata slots) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), slots.length)
            memptr := add(memptr, 0x40)
            let end := add(memptr, shl(5, slots.length))
            let calldataptr := slots.offset
            for {} 1 {} {
                mstore(memptr, tload(calldataload(calldataptr)))
                memptr := add(memptr, 0x20)
                calldataptr := add(calldataptr, 0x20)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }

    // Same shape, but returns the keys themselves: solc returns [0] for [0], not [7].
    function echoSlots(bytes32[] calldata slots) external view returns (bytes32[] memory) {
        assembly ("memory-safe") {
            let memptr := mload(0x40)
            let start := memptr
            mstore(memptr, 0x20)
            mstore(add(memptr, 0x20), slots.length)
            memptr := add(memptr, 0x40)
            let end := add(memptr, shl(5, slots.length))
            let calldataptr := slots.offset
            for {} 1 {} {
                mstore(memptr, calldataload(calldataptr))
                memptr := add(memptr, 0x20)
                calldataptr := add(calldataptr, 0x20)
                if iszero(lt(memptr, end)) { break }
            }
            return(start, sub(end, start))
        }
    }
}
