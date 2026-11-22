// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Root functions returning a scalar array. RootArrayReturnTwoSlots.sol is the same contract
// plus one unrelated state variable and one unused function.
// The importer lowers them the same way whatever the state-variable count (#2830): the exact
// batch and range slot reads keep their fixed lowerings, other tail assembly takes the ordinary
// lowering, and `T[] memory` results are ABI-encoded.
contract RootArrayReturnOneSlot {
    uint256[] private items = [7, 9];

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

    // Tail assembly that does not reference the bound array (here the named result) is not the
    // batch read: it takes the ordinary assembly lowering.
    function revertedWord(uint256 n) external view returns (bytes32[] memory r) {
        if (n > 0) {
            return r;
        }
        assembly {
            mstore(0, sload(0))
            revert(0, 0x20)
        }
    }

    function copied(uint256[] calldata xs) external pure returns (uint256[] memory) {
        return xs;
    }

    function narrowCopied(uint8[] calldata xs) external pure returns (uint8[] memory) {
        return xs;
    }

    function fromStorage() external view returns (uint256[] memory) {
        return items;
    }

    function built(uint256 x) external view returns (uint256[] memory r) {
        r = new uint256[](2);
        r[0] = x;
        r[1] = items[1] + x;
    }

}
