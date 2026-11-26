// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Yul `mcopy(dst, src, len)` (EIP-5656) between modelled `bytes memory` payloads:
// cursor-based multi-segment packing with copy to exact buffer end, forward and backward
// overlap (including aliased buffer references), runtime and literal `len = 0`, and
// unaligned 31-, 32-, and 33-byte copies.
contract SequenceFixture {
    uint256 private total;

    function _packTwoSegments(
        bytes memory segA,
        bytes memory segB,
        uint8 tagA,
        uint8 tagB
    ) internal pure returns (bytes memory) {
        uint256 lenA = segA.length;
        uint256 lenB = segB.length;
        require(lenA <= 0xffff && lenB <= 0xffff);
        uint256 bodyOffA = 4;
        uint256 bodyOffB = 6 + lenA;
        bytes memory buf = new bytes(bodyOffB + 2 + lenB);
        buf[0] = bytes1(tagA);
        buf[1] = bytes1(tagB);
        buf[2] = bytes1(uint8(lenA));
        buf[3] = bytes1(uint8(lenB));
        buf[bodyOffA] = bytes1(uint8(lenA >> 8));
        buf[bodyOffA + 1] = bytes1(uint8(lenA));
        assembly ("memory-safe") {
            let cursorA := add(add(buf, 0x20), bodyOffA)
            mcopy(add(cursorA, 2), add(segA, 0x20), lenA)
        }
        buf[bodyOffB] = bytes1(uint8(lenB >> 8));
        buf[bodyOffB + 1] = bytes1(uint8(lenB));
        assembly ("memory-safe") {
            let cursorB := add(add(buf, 0x20), bodyOffB)
            // Exact end of `buf`: `(bodyOffB + 2) + lenB == buf.length`.
            mcopy(add(cursorB, 2), add(segB, 0x20), lenB)
        }
        return buf;
    }

    function _sliceFromFoldedHeaderOffset(bytes memory raw) internal pure returns (bytes memory) {
        require(raw.length >= 54);
        uint256 tailLen = raw.length - 54;
        bytes memory sliced = new bytes(tailLen + 0);
        assembly ("memory-safe") {
            // `0x56 == 0x20 + 54`: folded header + 54-byte prefix offset.
            mcopy(add(sliced, 0x20), add(raw, 0x56), tailLen)
        }
        return sliced;
    }

    function _writeTailIntoBuffer(bytes memory out, bytes memory src) internal pure {
        require(out.length >= 36 && src.length >= 42);
        uint256 dstOff = 3;
        assembly ("memory-safe") {
            let outCursor := add(add(out, 0x20), dstOff)
            // 33-byte copy straddling a word boundary and ending at `out.length == 36`.
            mcopy(outCursor, add(src, 0x29), 33)
        }
    }

    function packAndSlice(
        bytes memory segA,
        bytes memory segB,
        uint256 mode
    ) external returns (bytes memory) {
        bytes memory res;
        uint256 sel = mode % 4;
        if (sel == 0) {
            res = _packTwoSegments(segA, segB, uint8(mode >> 8), uint8(mode >> 16));
        } else if (sel == 1) {
            bytes memory joined = _packTwoSegments(segA, segB, 0x11, 0x22);
            if (joined.length >= 10) {
                uint256 moveLen = joined.length - 4;
                assembly ("memory-safe") {
                    // Forward overlap (`dstStart > srcStart`) up to exact buffer end.
                    mcopy(add(joined, 0x24), add(joined, 0x21), moveLen)
                }
            }
            res = joined;
        } else if (sel == 2) {
            bytes memory joined = _packTwoSegments(segA, segB, 0x33, 0x44);
            if (joined.length >= 10) {
                uint256 moveLen = joined.length - 5;
                assembly ("memory-safe") {
                    // Backward overlap (`dstStart < srcStart`) from exact buffer end.
                    mcopy(add(joined, 0x21), add(joined, 0x25), moveLen)
                }
            }
            res = joined;
        } else {
            bytes memory padded = bytes.concat(
                abi.encodePacked(uint256(0x0102030405060708), uint160(0x090a0b0c0d), uint16(0x0e0f)),
                segA,
                segB
            );
            res = _sliceFromFoldedHeaderOffset(padded);
        }
        total = total + (uint256(keccak256(res)) % 1000);
        return res;
    }

    function _hashTwoSegments(uint256 x) internal pure returns (uint256) {
        uint64 a0 = uint64(x);
        uint32 a1 = uint32(x >> 64);
        bytes32 b0 = bytes32(x ^ 0xaa55aa55);
        uint8 b1 = uint8(x >> 8);
        bytes memory segA = abi.encodePacked(a0, a1);
        bytes memory segB = abi.encodePacked(b0, b1);
        bytes memory packed = _packTwoSegments(segA, segB, uint8(x), uint8(x >> 16));
        return uint256(keccak256(packed));
    }

    function change(uint256 x) external returns (uint256) {
        uint256 y;
        uint256 invX = ~x;
        uint256 arm = x % 8;
        if (arm == 0) {
            y = _hashTwoSegments(x);
        } else if (arm == 1) {
            // Overlapping forward copy (`dstStart > srcStart`) across word boundary.
            bytes memory buf = abi.encodePacked(x, invX);
            assembly ("memory-safe") {
                mcopy(add(buf, 0x25), add(buf, 0x20), 0x30)
            }
            y = uint256(keccak256(buf));
        } else if (arm == 2) {
            // Overlapping backward copy (`dstStart < srcStart`) reading to exact buffer end.
            uint256 w1 = (x >> 3) ^ 0x13579bdf;
            bytes memory buf = abi.encodePacked(invX, w1);
            assembly ("memory-safe") {
                mcopy(add(buf, 0x20), add(buf, 0x27), 0x39)
            }
            y = uint256(keccak256(buf));
        } else if (arm == 3) {
            // Runtime and literal `len == 0` copies preserve bytes and expand no memory.
            uint64 tail64 = uint64(x >> 12);
            bytes memory buf = abi.encodePacked(x, tail64);
            bytes memory empty = new bytes(0 + 0);
            uint256 zeroLen = x - x;
            assembly ("memory-safe") {
                mcopy(add(buf, 0x48), add(empty, 0x20), zeroLen)
                mcopy(add(empty, 0x20), add(buf, 0x99), 0)
            }
            y = uint256(keccak256(buf));
        } else if (arm == 4) {
            // 31-byte unaligned copy preserving sentinel bytes on both sides.
            bytes memory src = abi.encodePacked(x, invX);
            bytes memory dst = new bytes(20 + 20);
            dst[0] = bytes1(uint8(0x5a));
            dst[2] = bytes1(uint8(0x7e));
            dst[34] = bytes1(uint8(0xa5));
            dst[39] = bytes1(uint8(0x3c));
            assembly ("memory-safe") {
                mcopy(add(dst, 0x23), add(src, 0x25), 31)
            }
            y = uint256(keccak256(dst));
        } else if (arm == 5) {
            // 32-byte copy from folded `0x56` (`0x20 + 54`) offset.
            uint176 w2 = uint176(x >> 16);
            bytes memory raw = abi.encodePacked(x, invX, w2);
            bytes memory sliced = _sliceFromFoldedHeaderOffset(raw);
            y = uint256(keccak256(sliced));
        } else if (arm == 6) {
            // 33-byte copy through a void helper parameter cursor ending at exact buffer length.
            uint256 w2 = x ^ 0xfeedface;
            bytes memory src = abi.encodePacked(x, invX, w2);
            bytes memory out = new bytes(20 + 16);
            _writeTailIntoBuffer(out, src);
            y = uint256(keccak256(out));
        } else {
            // Overlapping forward copy through two aliased `bytes memory` references.
            bytes memory buf = abi.encodePacked(x, invX);
            bytes memory aliasBuf = buf;
            assembly ("memory-safe") {
                mcopy(add(aliasBuf, 0x24), add(buf, 0x20), 33)
            }
            y = uint256(keccak256(buf));
        }
        total = total + (y % 1000);
        return total;
    }

    function fail() external {
        total = total + 1;
        revert();
    }

    function read() external view returns (uint256) {
        return total;
    }
}
