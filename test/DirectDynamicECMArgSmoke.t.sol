// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// A direct dynamic parameter reaches an ECM as `data_offset, length` through `ecmCall`,
/// `ecmDo` and `ecmBind` alike, matching the model (`calldata = [0, length]` in the Lean
/// examples). The fixture modules expose `length`: `fromCall`/`fromBind` return it,
/// `fromDo` reverts when it exceeds 3.
contract DirectDynamicECMArgSmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.DirectDynamicECMArgSmoke", "DirectDynamicECMArgSmoke", _smokeYulDir()
        );
    }

    function testEcmCallSeesBytesLength() public {
        (bool ok, bytes memory data) = smoke.call(abi.encodeWithSignature("fromCall(bytes)", hex"010203"));
        assertTrue(ok);
        assertEq(abi.decode(data, (uint256)), 3);
    }

    function testEcmDoSeesStringLength() public {
        (bool ok,) = smoke.call(abi.encodeWithSignature("fromDo(string)", "abc"));
        assertTrue(ok, "length 3 accepted");
        (ok,) = smoke.call(abi.encodeWithSignature("fromDo(string)", "verity"));
        assertFalse(ok, "length 6 rejected by the module");
    }

    function testFuzzEcmCallLength(bytes calldata payload) public {
        (bool ok, bytes memory data) = smoke.call(abi.encodeWithSignature("fromCall(bytes)", payload));
        assertTrue(ok);
        assertEq(abi.decode(data, (uint256)), payload.length);
    }
}
