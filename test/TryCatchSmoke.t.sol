// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Records the last `notify(uint256)` argument.
contract NotifySink {
    uint256 public lastNotified;

    function notify(uint256 amount) external {
        lastNotified = amount;
    }
}

/// `tryCall (selfCall f(args))` is Solidity's `try this.f(args) {..} catch {..}`:
/// the compiled bytecode must actually run `f` and take the success branch when it
/// succeeds, as the Lean model (`Contract.selfCall`) says.
contract TryCatchSmokeTest is Test, YulTestBase {
    address internal smoke;
    address internal argSmoke;

    function setUp() public {
        smoke = deployCompiledVerityModule("Contracts.Smoke.TryCatchSmoke", "TryCatchSmoke", _smokeYulDir());
        argSmoke =
            deployCompiledVerityModule("Contracts.Smoke.TryCatchArgSmoke", "TryCatchArgSmoke", _smokeYulDir());
    }

    function _uint(address target, bytes memory callData) internal returns (uint256) {
        (bool ok, bytes memory data) = target.call(callData);
        assertTrue(ok, "call reverted");
        return abi.decode(data, (uint256));
    }

    function testSucceedingHopTakesSuccessBranch() public {
        // okHop writes 3, then the success branch writes 4 (Lean: `try_success_commits`).
        assertEq(_uint(smoke, abi.encodeWithSignature("catchOk()")), 4);
    }

    function testRevertingHopTakesCatchBranch() public {
        assertEq(_uint(smoke, abi.encodeWithSignature("catchFail()")), 2);
    }

    function testArgumentIsEncodedForHop() public {
        // Lean `tryCatchArgSevenValue`: hopWithArg(7) succeeds, success body writes 7 + 100.
        assertEq(_uint(argSmoke, abi.encodeWithSignature("catchArg(uint256)", 7)), 107);
        // Lean `tryCatchArgZeroValue`: hopWithArg(0) reverts, catch body writes 2.
        assertEq(_uint(argSmoke, abi.encodeWithSignature("catchArg(uint256)", 0)), 2);
    }

    function testFuzzArgumentReachesHop(uint128 amount) public {
        uint256 expected = amount == 0 ? 2 : uint256(amount) + 100;
        assertEq(_uint(argSmoke, abi.encodeWithSignature("catchArg(uint256)", uint256(amount))), expected);
    }

    function testHopWithExternalCallReceivesAllArguments() public {
        NotifySink sink = new NotifySink();
        assertEq(
            _uint(argSmoke, abi.encodeWithSignature("catchArgWithCall(address,uint256)", address(sink), 9)), 109
        );
        assertEq(sink.lastNotified(), 9, "hop forwarded the second argument");
    }
}
