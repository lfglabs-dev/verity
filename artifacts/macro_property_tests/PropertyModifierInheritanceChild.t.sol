// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyModifierInheritanceChildTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Helpers.lean
 */
contract PropertyModifierInheritanceChildTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("ModifierInheritanceChild", abi.encode(alice));
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
    // Property 2: bump has no unexpected revert
    function testAuto_Bump_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("bump()"));
        require(ok, "bump reverted unexpectedly");
    }
    // Property 3: setInherited has no unexpected revert
    function testAuto_SetInherited_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setInherited(uint256)", uint256(1)));
        require(ok, "setInherited reverted unexpectedly");
    }
}
