// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyInheritedRoleChildTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Helpers.lean
 */
contract PropertyInheritedRoleChildTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("InheritedRoleChild");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: audit enforces its required role
    function testAuto_Audit_RejectsUnauthorizedCaller() public {
        vm.prank(address(0x2222));
        (bool ok,) = target.call(abi.encodeWithSignature("audit()"));
        require(!ok, "audit accepted an unauthorized caller");
    }
}
