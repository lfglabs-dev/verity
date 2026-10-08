// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library BitMathLib {
    function zeroFloorSub(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := mul(gt(x, y), sub(x, y))
        }
    }

    function setBit(uint128 bitmap, uint256 bit) internal pure returns (uint128) {
        return uint128(bitmap | (1 << bit));
    }

    function clearBit(uint128 bitmap, uint256 bit) internal pure returns (uint128) {
        return uint128(bitmap & ~(1 << bit));
    }

    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + (a ^ b) / 2;
    }

    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
                result += 1;
            }
        }
        return result + (10 ** result < value ? 1 : 0);
    }

    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }
        uint256 result = 1 << (log2(a) >> 1);
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            uint256 candidate = a / result;
            return result < candidate ? result : candidate;
        }
    }
}

contract SequenceFixture {
    error BitwiseBlocked(uint256 input, uint128 mask);

    uint256 private accum;
    uint128 private bitmap;
    int256 private signedState;

    function change(uint256 input) external returns (uint256) {
        uint256 exp = (input == 19) ? 78 : (input % 6);
        uint256 scale = 10 ** exp;
        uint256 sq = (input % 1000) ** 2;
        uint8 wrappedPow;
        unchecked {
            wrappedPow = uint8((input % 15) + 2) ** uint8((input % 5) + 1);
        }

        uint256 bitIdx = input % 64;
        uint128 nextMap = BitMathLib.setBit(bitmap, bitIdx);
        nextMap = BitMathLib.clearBit(nextMap, (bitIdx + 1) % 64);
        nextMap |= uint128(1 << (input % 16));
        nextMap &= uint128(0x7fffffffffffffffffffffffffffffff);
        nextMap ^= ~uint128(input & 0xff);
        nextMap >>= uint8((input % 2) + 1);
        nextMap <<= uint8(input % 3);
        bitmap = nextMap;

        if (input == 21) {
            revert BitwiseBlocked(input, nextMap);
        }

        uint256 metric = BitMathLib.sqrt(sq + (input % 97))
            + BitMathLib.log10(scale + (input % 53))
            + BitMathLib.average(scale, sq)
            + BitMathLib.zeroFloorSub(sq + 10, input % 25);
        metric /= ((input % 3) + 1);
        metric %= 1000000007;

        int256 s = -int256((input % 128) + 16);
        s >>= uint8((input % 3) + 1);
        s <<= 1;
        s /= int256(2);
        signedState = s;

        accum += metric + uint256(nextMap) + uint256(wrappedPow) + uint256(s < 0 ? -s : s);
        require(input != 20, "bitwise exp rollback");
        return accum;
    }

    function fail() external {
        accum += 777;
        uint128 nextMap = bitmap;
        nextMap |= 3;
        bitmap = nextMap;
        revert BitwiseBlocked(777, nextMap);
    }

    function read() external view returns (uint256, uint128, int256) {
        return (accum, bitmap, signedState);
    }
}
