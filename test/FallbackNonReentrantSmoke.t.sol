// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Called by the smoke fallback; calls back into it once and records whether the reentry succeeded.
contract FallbackReenterer {
    bool public entered;
    bool public reentryOk;

    fallback() external {
        if (entered) return;
        entered = true;
        (bool ok,) = msg.sender.call(hex"deadbeef");
        reentryOk = ok;
    }
}

/// Calls the fallback twice within one call frame, so the transient lock of the first call is
/// still visible to the second unless the fallback released it.
contract SequentialCaller {
    function callTwice(address smoke) external returns (bool first, bool second) {
        (first,) = smoke.call(hex"deadbeef");
        (second,) = smoke.call(hex"deadbeef");
    }
}

/// `fallback nonreentrant(lock)` compiles to a transient-storage guard: a reentrant call into the
/// fallback reverts, and the lock is released when the outer call returns.
contract FallbackNonReentrantSmokeTest is Test, YulTestBase {
    address internal smoke;
    FallbackReenterer internal reenterer;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.FallbackNonReentrantSmoke", "FallbackNonReentrantSmoke", _smokeYulDir()
        );
        reenterer = new FallbackReenterer();
        (bool ok,) = smoke.call(abi.encodeWithSignature("setTarget(address)", address(reenterer)));
        assertTrue(ok, "setTarget reverted");
    }

    function _entryCount() internal returns (uint256) {
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature("entryCount()"));
        assertTrue(ok, "entryCount reverted");
        return abi.decode(out, (uint256));
    }

    function testReentrantFallbackCallReverts() public {
        (bool ok,) = smoke.call(hex"deadbeef");
        assertTrue(ok, "outer fallback call reverted");
        assertTrue(reenterer.entered(), "fallback did not call the target");
        assertFalse(reenterer.reentryOk(), "reentrant fallback call succeeded");
        assertEq(_entryCount(), 1);
    }

    function testLockReleasedAfterFallbackReturns() public {
        (bool first, bool second) = new SequentialCaller().callTwice(smoke);
        assertTrue(first && second, "a sequential fallback call reverted");
        assertEq(_entryCount(), 2);
    }
}
