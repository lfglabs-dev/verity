// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallUint256Bytes32AliasSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyDirectHelperCallUint256Bytes32AliasSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallUint256Bytes32AliasSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: rememberDigest has no unexpected revert
    function testAuto_RememberDigest_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("rememberDigest(bytes32)", bytes32(uint256(0xBEEF))));
        require(ok, "rememberDigest reverted unexpectedly");
    }
    // Property 2: run has no unexpected revert
    function testAuto_Run_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("run(uint256)", uint256(1)));
        require(ok, "run reverted unexpectedly");
    }
}
