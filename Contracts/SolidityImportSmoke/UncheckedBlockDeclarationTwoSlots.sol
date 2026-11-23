// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Helpers whose `unchecked` block declares locals and returns on some paths only.
// UncheckedBlockDeclarationTwoSlots.sol is the same contract plus one unrelated state variable
// and one unused function. The importer lowers them the same way whatever the state-variable
// count (#2830). The block's declarations are out of scope after it, also for inline assembly,
// which names the outer local or the constant they shadow.
contract UncheckedBlockDeclarationTwoSlots {
    uint256 private constant K = 11;
    uint256 private unrelated;

    function bumped(uint256 a) internal pure returns (uint256) {
        unchecked {
            uint256 t = a + 1;
            if (t == 0) return 7;
        }
        return a + 1;
    }

    function checkedAfter(uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            uint256 t = a * b;
            if (a == 0) return t;
        }
        return a + b;
    }

    function twoDeclarations(uint256 a) internal pure returns (uint256) {
        unchecked {
            uint256 t = a - 1;
            if (t > 100) return t;
            uint256 u = t * 2;
            if (u > 50) return u + 1;
        }
        return a;
    }

    function redeclared(uint256 a) internal pure returns (uint256) {
        unchecked {
            uint256 t = a - 1;
            if (a == 0) return t;
        }
        uint256 t = a * 3;
        return t;
    }

    function shadowedLocal(uint256 a) internal pure returns (uint256 r) {
        uint256 v = a;
        unchecked {
            uint256 v = a - 1;
            if (v == 0) return 100;
        }
        assembly {
            r := v
        }
    }

    function shadowedConstant(uint256 a) internal pure returns (uint256 r) {
        unchecked {
            uint256 K = a + 1;
            if (K == 0) return 3;
        }
        assembly {
            r := K
        }
    }

    function runBumped(uint256 x) external pure returns (uint256) {
        return bumped(x);
    }

    function runCheckedAfter(uint256 x, uint256 y) external pure returns (uint256) {
        return checkedAfter(x, y);
    }

    function runTwoDeclarations(uint256 x) external pure returns (uint256) {
        return twoDeclarations(x);
    }

    function runRedeclared(uint256 x) external pure returns (uint256) {
        return redeclared(x);
    }

    function runShadowedLocal(uint256 x) external pure returns (uint256) {
        return shadowedLocal(x);
    }

    function runShadowedConstant(uint256 x) external pure returns (uint256) {
        return shadowedConstant(x);
    }

    function unused() external {
        unrelated = 1;
    }
}
