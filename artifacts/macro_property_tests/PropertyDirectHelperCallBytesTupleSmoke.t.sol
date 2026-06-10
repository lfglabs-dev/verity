// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallBytesTupleSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyDirectHelperCallBytesTupleSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallBytesTupleSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: fanoutPayload decodes and matches the inferred tuple result
    function testAuto_FanoutPayload_ReturnsInferredTupleResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("fanoutPayload(bytes)", hex"CAFE"));
        require(ok, "fanoutPayload reverted unexpectedly");
        require(ret.length >= 64, "fanoutPayload ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, 0, "fanoutPayload tuple element 0 should preserve the inferred result");
        assertEq(actual1, 1, "fanoutPayload tuple element 1 should preserve the inferred result");
    }
    // Property 2: run decodes and matches the inferred tuple result
    function testAuto_Run_ReturnsInferredTupleResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("run(bytes)", hex"CAFE"));
        require(ok, "run reverted unexpectedly");
        require(ret.length >= 64, "run ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, 0, "run tuple element 0 should preserve the inferred result");
        assertEq(actual1, 1, "run tuple element 1 should preserve the inferred result");
    }
}
