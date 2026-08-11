// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyInheritedOverloadChildTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Helpers.lean
 */
contract PropertyInheritedOverloadChildTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("InheritedOverloadChild");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: inspect returns the direct parameter value
    function testAuto_Inspect_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("inspect(uint256)", uint256(1)));
        require(ok, "inspect reverted unexpectedly");
        assertEq(ret.length, 32, "inspect ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "inspect should preserve the expected value");
    }
    // Property 2: inspect returns the direct parameter value
    function testAuto_Inspect_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("inspect(address)", alice));
        require(ok, "inspect reverted unexpectedly");
        assertEq(ret.length, 32, "inspect ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, alice, "inspect should preserve the expected value");
    }
}
