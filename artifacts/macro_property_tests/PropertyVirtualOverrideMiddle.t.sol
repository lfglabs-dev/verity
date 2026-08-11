// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyVirtualOverrideMiddleTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Helpers.lean
 */
contract PropertyVirtualOverrideMiddleTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("VirtualOverrideMiddle", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: value returns the declared constant result
    function testAuto_Value_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("value()"));
        require(ok, "value reverted unexpectedly");
        assertEq(ret.length, 32, "value ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 2, "value should return the declared constant");
    }
}
