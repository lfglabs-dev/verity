// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library MaskLib {
    bytes16 internal constant LIB_MASK = 0xf00f00ff0000aaaa1111222233334444;
    bytes16 internal constant LIB_TAG = "0123456789abcdef";
    bytes8 internal constant HALF_MASK = 0x1122334455667788;
}

/// Neutral synthetic fixture exercising:
/// 1. `bytes16` / `bytesN` constants and bitmasks (hex, cast, unary `~`, shift, library constants).
/// 2. `while` loops with general scalar comparison conditions (`>`, `<`, `>=`, `<=`).
/// 3. Non-`.selector` `bytes4` expressions in `abi.encodeWithSelector` and selector checks.
contract FixedBytesConstWhileSelectorFixture {
    bytes16 public constant PUBLIC_MASK = 0x0102030405060708090a0b0c0d0e0f10;
    bytes16 private constant FLAG_MASK = 0x00ff00ff00ff00ff00ff00ff00ff00ff;
    bytes16 private constant INV_MASK = ~FLAG_MASK;
    bytes16 private constant ZERO_MASK = bytes16(0);
    bytes16 private constant SHIFTED_MASK = FLAG_MASK >> 8;
    bytes16 private constant CAST_MASK = bytes16(uint128(0xdeadbeef));
    bytes4 private constant FALLBACK_SEL = 0x12345678;

    error ZeroMask();
    error BlockedSelector(bytes4 sel);

    uint256 private lastTotal;
    bytes32 private lastDigest;

    function maskOps(bytes16 input, uint256 shiftAmt) external returns (bytes16) {
        if (input == ZERO_MASK) {
            revert ZeroMask();
        }
        bytes16 v = (input & FLAG_MASK) | (INV_MASK & MaskLib.LIB_MASK);
        v ^= SHIFTED_MASK ^ CAST_MASK ^ MaskLib.LIB_TAG;
        v &= 0xff00ff00ff00ff00ff00ff00ff00ff00;
        v |= bytes16(MaskLib.HALF_MASK);
        bytes16 shifted = (v >> (shiftAmt % 16)) ^ (v << (shiftAmt % 8));
        uint256 rawConst;
        assembly {
            rawConst := FLAG_MASK
        }
        lastTotal = rawConst >> 128;
        lastDigest = bytes32(shifted);
        return shifted;
    }

    function _helperWhileBreak(uint256 v, uint256 stopAt) internal pure returns (uint256 steps) {
        while (v > 1) {
            if (steps == stopAt) {
                break;
            }
            steps += 1;
            v >>= 1;
        }
    }

    function whileLoops(uint256 x, uint256 start, uint256 endVal, uint256 idx, uint256 limit)
        external
        returns (uint256)
    {
        uint256 acc = 0;

        // Right-shift with `> 1`
        uint256 s = x;
        while (s > 1) {
            acc += 1;
            s >>= 1;
        }

        // Division with `>= 2`
        uint256 d = x;
        while (d >= 2) {
            acc += 10;
            d /= 2;
        }

        // Bit-clearing with `> 1`
        uint256 b = x;
        while (b > 1) {
            acc += 100;
            b &= b - 1;
        }

        // Linear increasing `a < b`
        uint256 a = start;
        uint256 bound = endVal;
        while (a < bound) {
            acc += a;
            a += 1;
        }

        // Linear increasing `<=` with step 2
        uint256 p = start;
        while (p <= bound) {
            acc += 1;
            p += 2;
        }

        // Linear decreasing `idx >= limit` (panics with 0x11 if limit == 0)
        uint256 cur = idx;
        while (cur >= limit) {
            acc += cur;
            cur -= 1;
        }

        // Linear decreasing `>` with unchecked `--`
        uint256 down = idx;
        while (down > limit) {
            acc += 1;
            unchecked {
                --down;
            }
        }

        acc += _helperWhileBreak(x, 4);
        lastTotal = acc;
        return acc;
    }

    function encodeSelectors(
        bytes4 paramSel,
        bytes calldata rawCalldata,
        address target,
        uint256 amount
    ) external returns (bytes32) {
        bytes4 localSel = paramSel;
        bytes4 decodedSel = bytes4(rawCalldata);
        if (decodedSel == bytes4(0)) {
            revert BlockedSelector(decodedSel);
        }
        bytes32 d1 = keccak256(abi.encodeWithSelector(paramSel, target, amount));
        bytes32 d2 = keccak256(abi.encodeWithSelector(localSel, amount));
        bytes32 d3 = keccak256(abi.encodeWithSelector(decodedSel, target, amount));
        bytes32 d4 = keccak256(abi.encodeWithSelector(FALLBACK_SEL, amount));
        bytes32 d5 = keccak256(abi.encodeWithSelector(bytes4(keccak256("ping(uint256)")), amount));
        bytes32 d6 = keccak256(abi.encodeWithSelector(msg.sig, amount));
        bytes32 d7 = keccak256(abi.encodeWithSelector(0xabcdef01, amount));
        bytes32 combined = keccak256(abi.encode(d1, d2, d3, d4, d5, d6, d7));
        lastDigest = combined;
        return combined;
    }

    function read() external view returns (uint256, bytes32) {
        return (lastTotal, lastDigest);
    }
}
