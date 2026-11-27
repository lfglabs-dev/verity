// SPDX-License-Identifier: MIT
pragma solidity >=0.8.34 <0.9.0;

// Constant positive stride `for` loops (#2975): `i += k`, `i = i + k`, `i = k + i`,
// body-step `for (...; i < bound; ) { ... i += k; }`, pre-declared counters, wrap-free
// `unchecked` literal bounds, non-zero starts, helper `continue` / `break` / early
// `return`, root early `return`, and exact post-step `Panic(0x11)` overflow at `2^256`.
contract SequenceFixture {
    uint256 private total;
    uint256 private steps;

    function _sumChunks32(uint256 n) internal pure returns (uint256 acc) {
        for (uint256 i; i < n; i += 32) {
            acc += i + 1;
        }
    }

    function _sumTriples(uint256 start, uint256 bound) internal pure returns (uint256 acc) {
        for (uint256 i = start; i < bound; i = i + 3) {
            acc += i * 2 + 1;
        }
        for (uint256 j = start; j < bound; j = 3 + j) {
            acc += j + 5;
        }
    }

    function _scanHelper(
        uint256 n,
        uint256 skipVal,
        uint256 stopVal,
        uint256 retVal
    ) internal returns (uint256 acc) {
        for (uint256 i = 0; i < n; i += 3) {
            steps += 1;
            if (i == skipVal) {
                continue;
            }
            if (i == stopVal) {
                break;
            }
            if (i == retVal) {
                return acc + i + 1000;
            }
            acc += i + 2;
        }
        return acc + 500;
    }

    function _boundaryReturn(uint256 mode) internal returns (uint256) {
        uint256 start = type(uint256).max - 63;
        for (uint256 i = start; i < type(uint256).max; i += 32) {
            steps += 1;
            if (i > type(uint256).max - 32) {
                if (mode == 1) {
                    return 77;
                }
                if (mode == 2) {
                    continue;
                }
            }
        }
        return 11;
    }

    function _boundaryBreak(uint256 shouldBreak) internal returns (uint256 count) {
        uint256 start = type(uint256).max - 63;
        for (uint256 i = start; i < type(uint256).max; i += 32) {
            steps += 1;
            count += 1;
            if (shouldBreak == 1 && i > type(uint256).max - 32) {
                break;
            }
        }
    }

    function change(uint256 x) external returns (uint256) {
        if (x == type(uint256).max) {
            steps += 5;
            return _boundaryReturn(0);
        }
        if (x == type(uint256).max - 1) {
            uint256 v = _boundaryReturn(1);
            total += v;
            return total;
        }
        if (x == type(uint256).max - 2) {
            steps += 5;
            return _boundaryReturn(2);
        }
        if (x == type(uint256).max - 3) {
            uint256 v = _boundaryBreak(1);
            total += v;
            return total;
        }
        if (x == type(uint256).max - 4) {
            steps += 5;
            return _boundaryBreak(0);
        }
        if (x == type(uint256).max - 5) {
            for (uint256 i = type(uint256).max - 63; i < type(uint256).max; i += 32) {
                steps += 1;
                if (i > type(uint256).max - 32) {
                    total += 91;
                    return total;
                }
            }
        }
        if (x == type(uint256).max - 6) {
            for (uint256 i = type(uint256).max - 63; i < type(uint256).max - 31; i += 32) {
                steps += 1;
                total += 13;
            }
            return total;
        }
        if (x == type(uint256).max - 7) {
            steps += 5;
            for (uint256 i = type(uint256).max - 63; i < type(uint256).max - 30; i += 32) {
                steps += 1;
                total += 17;
            }
            return total;
        }

        uint256 n32 = x % 97;
        uint256 n3 = (x >> 7) % 13;
        uint256 s3 = (x >> 11) % 10;
        uint256 acc = _sumChunks32(n32) + _sumTriples(s3, n3);

        uint256 p = 9;
        for (p = 1; p < n3; p += 3) {
            acc += p;
        }
        acc += p * 10;

        for (uint256 b = 0; b < n3; ) {
            acc += b + 1;
            b += 3;
        }

        unchecked {
            for (uint256 u = 0; u < 10; u += 3) {
                acc += u;
            }
        }

        uint256 skipVal = ((x >> 15) % 4) * 3;
        uint256 stopVal = ((x >> 17) % 5) * 3;
        uint256 retVal = ((x >> 20) % 5) * 3;
        acc += _scanHelper(n3 * 2, skipVal, stopVal, retVal);

        total += acc;
        steps += 1;
        return total;
    }

    function fail() external {
        steps += 99;
        total += _boundaryReturn(0);
    }

    function read() external view returns (uint256, uint256) {
        return (total, steps);
    }
}
