// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallProjectedBytesArgSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyDirectHelperCallProjectedBytesArgSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallProjectedBytesArgSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: consumePayload returns the declared constant result
    function testAuto_ConsumePayload_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("consumePayload(bytes)", hex"CAFE"));
        require(ok, "consumePayload reverted unexpectedly");
        assertEq(ret.length, 32, "consumePayload ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 1, "consumePayload should return the declared constant");
    }
    // Property 2: TODO decode and assert `run` result
    function testTODO_Run_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("run((address,bytes,uint256)[],uint256)", abi.decode(abi.encode(uint256(0)), ((address,bytes,uint256)[])), uint256(1)));
        require(ok, "run reverted unexpectedly");
        assertEq(ret.length, 32, "run ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
