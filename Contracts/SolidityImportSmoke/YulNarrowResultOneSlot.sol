// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Yul writes to narrow named results and narrow locals keep the raw word, as solc does in
/// both pipelines: a later Yul read sees it, copies and internal arguments pass it on, and
/// Solidity consumers (`==`, `!`, conditions, storage, mapping keys, ABI encoding) clean it.
/// The pair helper writes a `bool` and a `uint32` result from two scratch words; `tryMul`
/// writes its `bool` result from a Yul expression and reads it back through a `bool`
/// parameter. Paired with `YulNarrowResultTwoSlots.sol` (one more state variable).
library YulNarrowResultLib {
    function pair(uint256 a, uint256 b) internal pure returns (bool flag, uint32 width) {
        assembly ("memory-safe") {
            mstore(0x00, a)
            mstore(0x20, b)
            flag := mload(0x00)
            width := mload(0x20)
        }
    }

    function tryMul(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
        unchecked {
            uint256 c = a * b;
            assembly ("memory-safe") {
                success := or(eq(div(c, a), b), iszero(a))
            }
            result = c * toUint(success);
        }
    }

    function toUint(bool b) internal pure returns (uint256 u) {
        assembly ("memory-safe") {
            u := iszero(iszero(b))
        }
    }

    function saturatingMul(uint256 a, uint256 b) internal pure returns (uint256) {
        (bool success, uint256 result) = tryMul(a, b);
        return success ? result : type(uint256).max;
    }

    /// A single named `bool` result read back in Yul.
    function readBack(uint256 w) internal pure returns (bool flag) {
        assembly ("memory-safe") {
            flag := w
            flag := eq(flag, w)
        }
    }

    /// A single named `uint8` result written by Solidity arithmetic, then read in Yul.
    function square(uint8 a) internal pure returns (uint8 s) {
        unchecked {
            s = a * a;
        }
        assembly ("memory-safe") {
            s := shr(0, s)
        }
    }
}

contract YulNarrowResultOneSlot {
    mapping(bool => uint256) private marks;

    function pairWords(uint256 a, uint256 b) external pure returns (bool, uint32) {
        return YulNarrowResultLib.pair(a, b);
    }

    function pairRaw(uint256 a, uint256 b) external pure returns (uint256 r, uint256 q) {
        (bool flag, uint32 width) = YulNarrowResultLib.pair(a, b);
        assembly ("memory-safe") {
            r := flag
            q := width
        }
    }

    function pairUse(uint256 a, uint256 b) external pure returns (uint256) {
        (bool flag, uint32 width) = YulNarrowResultLib.pair(a, b);
        if (flag && width > 0) return uint256(width) + 1;
        return 0;
    }

    function mulSat(uint256 a, uint256 b) external pure returns (uint256) {
        return YulNarrowResultLib.saturatingMul(a, b);
    }

    function mulTry(uint256 a, uint256 b) external pure returns (bool, uint256) {
        return YulNarrowResultLib.tryMul(a, b);
    }

    function readBackRaw(uint256 w) external pure returns (uint256 r) {
        bool flag = YulNarrowResultLib.readBack(w);
        assembly ("memory-safe") {
            r := flag
        }
    }

    function squareRaw(uint8 a) external pure returns (uint256 r) {
        uint8 s = YulNarrowResultLib.square(a);
        assembly ("memory-safe") {
            r := s
        }
    }

    function localWord(uint256 w) external pure returns (bool flag, uint256 raw, uint256 copied) {
        bool b;
        assembly ("memory-safe") {
            b := w
        }
        flag = b;
        bool c = b;
        assembly ("memory-safe") {
            raw := b
            copied := c
        }
    }

    function localUses(uint256 w) external pure returns (uint256 r) {
        bool b;
        assembly ("memory-safe") {
            b := w
        }
        bool n = !b;
        bool c = true && b;
        uint256 notWord;
        uint256 andWord;
        assembly ("memory-safe") {
            notWord := n
            andWord := c
        }
        r = (b == true ? 1 : 0) + (b ? 10 : 0) + notWord * 100 + andWord * 1000;
    }

    function localKey(uint256 w) external returns (uint256) {
        bool b;
        assembly ("memory-safe") {
            b := w
        }
        marks[b] = 7;
        return marks[true];
    }
}
