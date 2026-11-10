// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// `return ()` in a `Unit` function exits early: externally it ends the call with the
/// writes so far committed, in an internal helper it resumes the caller. The expected
/// values are the `decide` examples in `Contracts/Smoke/UnitReturnSmoke.lean`.
contract UnitReturnSmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule("Contracts.Smoke.UnitReturnSmoke", "UnitReturnSmoke", _smokeYulDir());
    }

    function _bumpThenRead(uint256 x) internal returns (uint256 hits, uint256 afterCount) {
        (bool ok, bytes memory ret) = smoke.call(abi.encodeWithSignature("bumpTwice(uint256)", x));
        assertTrue(ok, "bumpTwice reverted");
        assertEq(ret.length, 0, "Unit function returns no data");
        (ok, ret) = smoke.call(abi.encodeWithSignature("hitsAndAfter()"));
        assertTrue(ok, "hitsAndAfter reverted");
        return abi.decode(ret, (uint256, uint256));
    }

    function testHelperEarlyReturnResumesCaller() public {
        (uint256 hits, uint256 afterCount) = _bumpThenRead(0);
        assertEq(hits, 0);
        assertEq(afterCount, 1, "caller continued after the helper's return ()");
    }

    function testNoEarlyReturn() public {
        (uint256 hits, uint256 afterCount) = _bumpThenRead(3);
        assertEq(hits, 6);
        assertEq(afterCount, 1);
    }

    function testExternalEarlyReturnCommitsAndStops() public {
        (uint256 hits, uint256 afterCount) = _bumpThenRead(7);
        assertEq(hits, 7, "second bump skipped");
        assertEq(afterCount, 1, "writes before return () committed");
    }
}
