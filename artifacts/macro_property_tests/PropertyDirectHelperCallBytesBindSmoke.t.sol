// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallBytesBindSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyDirectHelperCallBytesBindSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallBytesBindSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: samePayload matches the expected dynamic-parameter comparison result
    function testAuto_SamePayload_ComparesDirectDynamicParamsEq() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("samePayload(bytes,bytes)", hex"CAFE", hex"CAFE"));
        require(ok, "samePayload reverted unexpectedly");
        assertEq(ret.length, 32, "samePayload ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        bool expected = true;
        assertEq(actual, expected, "samePayload should preserve the configured comparison result");
        assertTrue(actual, "samePayload should return true for the configured bytes comparison");
    }
    // Property 2: run decodes and matches the inferred straight-line result
    function testAuto_Run_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("run(bytes)", hex"CAFE"));
        require(ok, "run reverted unexpectedly");
        assertEq(ret.length, 32, "run ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, (hex"CAFE" == hex"CAFE"), "run should preserve the inferred result");
    }
}
