// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyPayableFallbackSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Declarations.lean
 */
contract PropertyPayableFallbackSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("PayableFallbackSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: getFallbackValue reads storage slot 0 and decodes the result
    function testAuto_GetFallbackValue_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getFallbackValue()"));
        require(ok, "getFallbackValue reverted unexpectedly");
        assertEq(ret.length, 32, "getFallbackValue ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getFallbackValue should return storage slot 0");
    }
}
