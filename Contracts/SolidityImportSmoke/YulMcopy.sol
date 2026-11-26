// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Yul `mcopy` shapes outside the modeled scratch-space slice (YulMcopyChecks.lean).
contract YulMcopy {
    function unwrittenSource(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mcopy(0x20, 0x00, 0x20)
            y := add(x, 1)
        }
    }
    function sizedCopy(uint256 n) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, n)
            mcopy(0x20, 0x00, n)
            y := n
        }
    }
    function freePointerDestination(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, x)
            mcopy(0x30, 0x00, 0x20)
            y := x
        }
    }
    function freePointerSource(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, x)
            mstore(0x20, x)
            let p := mload(0x40)
            mstore(0x40, p)
            mcopy(0x00, 0x20, 0x40)
            y := mload(0x00)
        }
    }
    function partlyWrittenSource(uint256 x) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mstore(0x00, x)
            mcopy(0x00, 0x10, 0x20)
            y := mload(0x00)
        }
    }
    function bufferCopy(bytes memory target, bytes memory source) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            mcopy(add(target, 0x20), add(source, 0x20), mload(source))
        }
        y = target.length;
    }
    function unknownDestinationPointer(uint256 ptr, bytes memory source) external pure returns (uint256 y) {
        require(source.length >= 4);
        assembly ("memory-safe") {
            mcopy(ptr, add(source, 0x20), 4)
        }
        y = source.length;
    }
    function unknownSourcePointer(bytes memory target, uint256 ptr) external pure returns (uint256 y) {
        require(target.length >= 4);
        assembly ("memory-safe") {
            mcopy(add(target, 0x20), ptr, 4)
        }
        y = target.length;
    }
    function headerDestination(bytes memory target, bytes memory source) external pure returns (uint256 y) {
        require(target.length >= 32 && source.length >= 4);
        assembly ("memory-safe") {
            mcopy(add(target, 0x10), add(source, 0x20), 4)
        }
        y = target.length;
    }
    function pastEndDestination(bytes memory source, uint256 n) external pure returns (bytes memory) {
        require(n <= 64 && n <= source.length);
        bytes memory out = new bytes(n + 2);
        assembly ("memory-safe") {
            mcopy(add(out, 0x24), add(source, 0x20), n)
        }
        return out;
    }
    function uncheckedWrapGuard(
        bytes memory target,
        bytes memory source,
        uint256 off,
        uint256 len
    ) external pure returns (uint256 y) {
        unchecked {
            require(off + len <= target.length && len <= source.length);
        }
        assembly ("memory-safe") {
            let dst := add(add(target, 0x20), off)
            mcopy(dst, add(source, 0x20), len)
        }
        y = target.length;
    }
    function escapedCursor(bytes memory target) external pure returns (uint256 y) {
        assembly ("memory-safe") {
            let cur := add(target, 0x20)
            y := cur
        }
    }
    function singleArmIfLengthOverwrite(uint256 flag) external pure returns (uint256) {
        bytes memory dst = new bytes(2 + 2);
        bytes memory next = abi.encode(uint256(0xdeadbeef));
        bytes memory src = abi.encode(uint256(0x11111111), uint256(0));
        uint256 len = 64;
        if (flag != 0) {
            len = 64;
        }
        assembly ("memory-safe") {
            mcopy(add(dst, 0x20), add(src, 0x20), len)
        }
        return abi.decode(next, (uint256));
    }
    function _shortBranch(bytes32 word, bool pick) internal pure returns (string memory) {
        if (pick) {
            string memory str = new string(32);
            assembly ("memory-safe") {
                mstore(str, 64)
                mstore(add(str, 0x20), word)
            }
            return str;
        }
        return "ok";
    }
    function branchingShortStringAlias(uint256 x, bool pick) external pure returns (uint256) {
        bytes memory b1 = bytes(_shortBranch(bytes32(x), pick));
        bytes memory b2 = b1;
        bytes memory out = new bytes(64 + 0);
        assembly ("memory-safe") {
            mcopy(add(out, 0x20), add(b2, 0x20), 64)
        }
        return uint256(keccak256(out));
    }
    function loopBackEdgeShortStringSource(uint256 x) external pure returns (uint256) {
        bytes memory cur = new bytes(64 + 0);
        bytes memory out = new bytes(64 + 0);
        for (uint256 i = 0; i < 2; i++) {
            assembly ("memory-safe") {
                mcopy(add(out, 0x20), add(cur, 0x20), 64)
            }
            cur = bytes(_shortBranch(bytes32(x), true));
        }
        return uint256(keccak256(out));
    }
    function rightToLeftCallOffset(address target) external view returns (uint256) {
        bytes memory dst = new bytes(16 + 16);
        bytes memory src = abi.encodePacked(uint8(0xff), uint24(0));
        assembly ("memory-safe") {
            mcopy(
                add(add(dst, 0x20), and(returndatasize(), 3)),
                add(src, 0x20),
                staticcall(gas(), target, 0, 0, 0, 0)
            )
        }
        return abi.decode(dst, (uint256));
    }
    function rightToLeftCursorOffset(address target) external view returns (uint256) {
        bytes memory dst = new bytes(16 + 16);
        bytes memory src = abi.encodePacked(uint8(0xa5), uint24(0));
        assembly ("memory-safe") {
            let cur := add(
                add(dst, 0x20),
                add(and(returndatasize(), 3), staticcall(gas(), target, 0, 0, 0, 0))
            )
            mcopy(cur, add(src, 0x20), 1)
        }
        return abi.decode(dst, (uint256));
    }
}
contract YulMcopyStateful {
    struct SlotEntry {
        uint256 val;
    }
    SlotEntry[] private entries;
    function _slotAt(
        SlotEntry[] storage arr,
        uint256 idx
    ) private pure returns (SlotEntry storage r) {
        assembly ("memory-safe") {
            let base := arr.slot
            r.slot := add(base, idx)
        }
    }
    function repeatedStoragePointerHelper() external view returns (uint256) {
        return _slotAt(entries, 0).val + _slotAt(entries, 1).val;
    }
    function _clobberPrefix(bytes memory dst, bytes memory zeroes) private pure {
        require(dst.length >= 13 && zeroes.length >= 13);
        assembly ("memory-safe") {
            mcopy(add(dst, 0x20), add(zeroes, 0x20), 13)
        }
    }
    function create2ClobberedViaAlias(bytes32 salt) external returns (address addr) {
        bytes memory code = abi.encodePacked(hex"600d380380600d6000396000f3", uint8(0x00));
        bytes memory aliasCode = code;
        bytes memory zeroes = new bytes(10 + 6);
        assembly ("memory-safe") {
            mcopy(add(aliasCode, 0x20), add(zeroes, 0x20), 13)
            addr := create2(0, add(code, 0x20), mload(code), salt)
        }
    }
    function create2ClobberedViaLoop(bytes32 salt) external returns (address addr) {
        bytes memory code = abi.encodePacked(hex"600d380380600d6000396000f3", uint8(0x00));
        bytes memory zeroes = new bytes(10 + 6);
        for (uint256 i = 0; i < 2; i++) {
            uint256 stepSalt = uint256(salt) + i;
            assembly ("memory-safe") {
                addr := create2(0, add(code, 0x20), mload(code), stepSalt)
                mcopy(add(code, 0x20), add(zeroes, 0x20), 13)
            }
        }
    }
    function create2ClobberedViaHelper(bytes32 salt) external returns (address addr) {
        bytes memory code = abi.encodePacked(hex"600d380380600d6000396000f3", uint8(0x00));
        bytes memory zeroes = new bytes(10 + 6);
        _clobberPrefix(code, zeroes);
        assembly ("memory-safe") {
            addr := create2(0, add(code, 0x20), mload(code), salt)
        }
    }
}
