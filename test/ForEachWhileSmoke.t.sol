// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Solidity loops with `break`, the behaviour `Stmt.forEachWhile` lowers to (#2916).
/// Each function returns `hit * 2^255 + found * 2^128 + iterations`.
contract ForEachWhileSmokeReference {
    function _pack(uint256 hit, uint256 found, uint256 iters) internal pure returns (uint256) {
        unchecked {
            return hit * 2 ** 255 + found * 2 ** 128 + iters;
        }
    }

    function firstMatch(uint256 n, uint256 target) public pure returns (uint256) {
        uint256 hit;
        uint256 found;
        uint256 iters;
        unchecked {
            for (uint256 i = 0; i < n; i++) {
                iters++;
                if (i == target) {
                    found = i;
                    hit = 1;
                    break;
                }
            }
        }
        return _pack(hit, found, iters);
    }

    function firstMatchForEach(uint256 n, uint256 target) external pure returns (uint256) {
        return firstMatch(n, target);
    }

    /// The guard reads the loop variable before the iteration rebinds it.
    function countWhileBelow(uint256 n, uint256 limit) external pure returns (uint256) {
        uint256 i;
        uint256 found;
        uint256 iters;
        unchecked {
            for (uint256 idx = 0; idx < n && i < limit; idx++) {
                i = idx;
                iters++;
                found = i;
            }
        }
        return _pack(0, found, iters);
    }

    function emptyLoop(uint256 n) external pure returns (uint256) {
        uint256 sink;
        for (uint256 i = 0; i < n;) {
            assembly {
                sink := add(sink, 0)
            }
            unchecked {
                i++;
            }
        }
        return 7 + sink;
    }

    /// The guard evaluates to the even nonzero word `2` while `i < limit`, exercising
    /// `iszero(iszero(guard))` normalization in `and(lt(idx, cnt), iszero(iszero(guard)))`.
    function evenWordGuard(uint256 n, uint256 limit) external pure returns (uint256) {
        uint256 i;
        uint256 found;
        uint256 iters;
        unchecked {
            for (uint256 idx = 0; idx < n && ((i < limit ? 2 : 0) != 0); idx++) {
                i = idx;
                iters++;
                found = i;
            }
        }
        return _pack(0, found, iters);
    }
}

/// The compiled `Contracts.Smoke.ForEachWhileSmoke` against the reference: equal results,
/// and the same success or out-of-gas failure under a gas cap.
contract ForEachWhileSmokeTest is Test, YulTestBase {
    address internal smoke;
    address internal ref;

    uint256 internal constant GAS_CAP = 3_000_000;
    uint256 internal constant HUGE = 2 ** 200;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.ForEachWhileSmoke", "ForEachWhileSmoke", _smokeYulDir()
        );
        ref = address(new ForEachWhileSmokeReference());
    }

    function _pack(uint256 hit, uint256 found, uint256 iters) internal pure returns (uint256) {
        return hit * 2 ** 255 + found * 2 ** 128 + iters;
    }

    function _both(bytes memory data) internal returns (bool okV, bytes memory outV) {
        bool okR;
        bytes memory outR;
        (okV, outV) = smoke.call{gas: GAS_CAP}(data);
        (okR, outR) = ref.call{gas: GAS_CAP}(data);
        assertEq(okV, okR, "success differs from the Solidity reference");
        if (okV) assertEq(outV, outR, "result differs from the Solidity reference");
    }

    function _value(bytes memory data) internal returns (uint256) {
        (bool ok, bytes memory out) = _both(data);
        assertTrue(ok, "call failed");
        return abi.decode(out, (uint256));
    }

    function _firstMatch(uint256 n, uint256 target) internal returns (uint256) {
        return _value(abi.encodeWithSignature("firstMatch(uint256,uint256)", n, target));
    }

    function testMatchOnFirstIteration() public {
        assertEq(_firstMatch(10, 0), _pack(1, 0, 1));
    }

    function testMatchOnMiddleIteration() public {
        assertEq(_firstMatch(10, 4), _pack(1, 4, 5));
    }

    function testMatchOnLastIteration() public {
        assertEq(_firstMatch(10, 9), _pack(1, 9, 10));
    }

    function testNoMatch() public {
        assertEq(_firstMatch(10, 10), _pack(0, 0, 10));
    }

    function testZeroCount() public {
        assertEq(_firstMatch(0, 0), _pack(0, 0, 0));
        assertEq(_value(abi.encodeWithSignature("emptyLoop(uint256)", 0)), 7);
    }

    function testEmptyLoop() public {
        assertEq(_value(abi.encodeWithSignature("emptyLoop(uint256)", 25)), 7);
    }

    /// The early exit stops the loop: a huge count still succeeds under the gas cap.
    function testHugeCountWithEarlyExit() public {
        assertEq(_firstMatch(HUGE, 3), _pack(1, 3, 4));
        assertEq(_firstMatch(type(uint256).max, 0), _pack(1, 0, 1));
    }

    /// Without an exit both sides run out of gas.
    function testHugeCountWithoutExitRunsOutOfGasOnBothSides() public {
        (bool ok,) = _both(abi.encodeWithSignature("firstMatch(uint256,uint256)", HUGE, HUGE));
        assertFalse(ok);
        (ok,) = _both(abi.encodeWithSignature("emptyLoop(uint256)", HUGE));
        assertFalse(ok);
        (ok,) = _both(abi.encodeWithSignature("countWhileBelow(uint256,uint256)", HUGE, HUGE));
        assertFalse(ok);
        (ok,) = _both(abi.encodeWithSignature("evenWordGuard(uint256,uint256)", HUGE, HUGE));
        assertFalse(ok);
    }

    /// Control: the plain `forEach` flag loop agrees on results, but runs every remaining
    /// iteration after the match, so it runs out of gas where the reference returns.
    function testForEachFlagLoopKeepsIterating() public {
        assertEq(
            _value(abi.encodeWithSignature("firstMatchForEach(uint256,uint256)", 10, 4)),
            _pack(1, 4, 5)
        );
        (bool okV,) = smoke.call{gas: GAS_CAP}(
            abi.encodeWithSignature("firstMatchForEach(uint256,uint256)", HUGE, 3)
        );
        (bool okR,) = ref.call{gas: GAS_CAP}(
            abi.encodeWithSignature("firstMatchForEach(uint256,uint256)", HUGE, 3)
        );
        assertFalse(okV);
        assertTrue(okR);
    }

    /// The guard reads the loop variable's previous value: with `limit = 1` the loop runs
    /// indices 0 and 1, then stops.
    function testGuardReadsLoopVariable() public {
        bytes4 sel = bytes4(keccak256("countWhileBelow(uint256,uint256)"));
        assertEq(_value(abi.encodeWithSelector(sel, 10, 1)), _pack(0, 1, 2));
        assertEq(_value(abi.encodeWithSelector(sel, 10, 0)), _pack(0, 0, 0));
        assertEq(_value(abi.encodeWithSelector(sel, 10, 5)), _pack(0, 5, 6));
        assertEq(_value(abi.encodeWithSelector(sel, 3, 100)), _pack(0, 2, 3));
        assertEq(_value(abi.encodeWithSelector(sel, HUGE, 7)), _pack(0, 7, 8));
    }

    /// An even nonzero guard word (`2`) must still enter the loop via `iszero(iszero(guard))`
    /// where raw bitwise `and(1, 2)` would evaluate to `0`.
    function testEvenNonzeroWordGuard() public {
        bytes4 sel = bytes4(keccak256("evenWordGuard(uint256,uint256)"));
        assertEq(_value(abi.encodeWithSelector(sel, 10, 5)), _pack(0, 5, 6));
        assertEq(_value(abi.encodeWithSelector(sel, 10, 0)), _pack(0, 0, 0));
        assertEq(_value(abi.encodeWithSelector(sel, HUGE, 4)), _pack(0, 4, 5));
    }

    function testFirstMatchFuzz(uint256 n, uint256 target) public {
        n = bound(n, 0, 300);
        target = bound(target, 0, 400);
        _firstMatch(n, target);
        _value(abi.encodeWithSignature("firstMatchForEach(uint256,uint256)", n, target));
    }

    function testCountWhileBelowFuzz(uint256 n, uint256 limit) public {
        n = bound(n, 0, 300);
        limit = bound(limit, 0, 400);
        _value(abi.encodeWithSignature("countWhileBelow(uint256,uint256)", n, limit));
    }
}
