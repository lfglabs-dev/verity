// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract HelperLoopEarlyExitTwoSlots {
    uint256 private hits;
    uint256 private spare;

    function _at(uint256 packed, uint256 i) private pure returns (uint32) {
        return uint32(packed >> (i * 32));
    }

    function _contains(uint256 packed, uint256 n, uint32 id) private returns (bool) {
        for (uint256 i = 0; i < n; ++i) {
            hits += 1;
            if (_at(packed, i) == id) return true;
        }
        return false;
    }

    function _unconditionalReturn(uint256 n) internal pure returns (uint256) {
        for (uint256 i = 0; i < n; i++) {
            return i + 7;
        }
        return 0;
    }

    function _conditionalReturn(uint256 n) internal pure returns (uint256) {
        for (uint256 i = 0; i < n; i++) {
            if (i == 1) return i + 10;
        }
        return 0;
    }

    function _uint16BoundReturn(uint16 n) internal pure returns (uint256) {
        for (uint256 i = 0; i < n; i++) {
            if (i == 260) return i;
        }
        return 0;
    }

    function _literal257Return(uint256 target) internal pure returns (uint256) {
        for (uint256 i = 0; i < 257; i++) {
            if (i == target) return i + 1;
        }
        return 0;
    }

    function _unboundedBreak(uint256 n, uint256 stopAt) internal returns (uint256 count) {
        for (uint256 i = 0; i < n; i++) {
            if (i == stopAt) {
                break;
            }
            hits += 1;
            count += 1;
        }
    }

    function _predeclaredReturn(uint256 n, uint256 target) internal pure returns (uint256) {
        uint256 i;
        for (i = 0; i < n; i++) {
            if (i == target) return i + 50;
        }
        return i + 1000;
    }

    function runContains(uint256 packed, uint256 n, uint32 id) external returns (uint256) {
        bool ok = _contains(packed, n, id);
        return (ok ? 1000 : 0) + hits;
    }

    function runUnconditionalReturn(uint256 n) external pure returns (uint256) {
        return _unconditionalReturn(n);
    }

    function runConditionalReturn(uint256 n) external pure returns (uint256) {
        return _conditionalReturn(n);
    }

    function runUint16BoundReturn(uint256 x) external pure returns (uint256) {
        return _uint16BoundReturn(uint16(x));
    }

    function runLiteral257Return(uint256 target) external pure returns (uint256) {
        return _literal257Return(target);
    }

    function runUnboundedBreak(uint256 n, uint256 stopAt) external returns (uint256) {
        uint256 c = _unboundedBreak(n, stopAt);
        return c * 1000 + hits;
    }

    function runPredeclaredReturn(uint256 n, uint256 target) external pure returns (uint256) {
        return _predeclaredReturn(n, target);
    }
}
