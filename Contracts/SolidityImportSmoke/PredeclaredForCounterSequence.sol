// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `for (i = 0; i < n; ...)` over a counter declared before the loop: the body reads the
// counter, and after the loop the local holds its exit value `n`. Root and helper loops,
// a reused counter with a prior value, a narrow counter whose checked increment panics,
// and `continue` (the counter still advances).
contract SequenceFixture {
    uint256 private total;
    uint256 private last;

    function _sumNarrow(uint256 n) internal pure returns (uint256) {
        uint256 acc;
        uint8 j;
        for (j = 0; j < n; j++) {
            acc += uint256(j) * 3 + 1;
        }
        return acc + j;
    }

    function _skipThirds(uint256 n) internal pure returns (uint256 acc) {
        uint256 k = 5;
        for (k = 0; k < n; ++k) {
            if (k % 3 == 2) {
                continue;
            }
            acc += k;
        }
        acc += k * 100;
    }

    function change(uint256 x) external returns (uint256 result) {
        if (x == 19) {
            for (x = 0; x < 3; ++x) {
                total += x;
            }
            total += x;
            return total;
        }
        if (x == 257) {
            uint8 dirty;
            assembly { dirty := x }
            uint16 mixed = dirty | uint16(2);
            uint256 k;
            for (k = 0; k < mixed; ++k) {
                total += 1;
            }
            last += k;
            int8 signedByte = 0;
            assembly { signedByte := x }
            int256 widened = signedByte;
            uint256 bound = uint256(widened);
            for (k = 0; k < bound; ++k) { total += 1; }
            last += k;
            return (dirty);
        }
        if (x == 17) {
            result = 99;
            for (result = 0; result < result; result++) {
                total += 1;
            }
            return result;
        }
        uint256 n = x % 40;
        uint256 i;
        uint256 s;
        for (i = 0; i < n; ++i) {
            s += i * i;
        }
        last = i;
        if (x % 2 == 1) {
            for (i = 0; i < 4; i++) {
                s += i;
            }
        }
        total += s + i * 1000 + _sumNarrow(x % 300) + _skipThirds(x % 17);
        return total;
    }

    function fail() external {
        total += _sumNarrow(256);
    }

    function read() external view returns (uint256, uint256) {
        return (total, last);
    }
}
