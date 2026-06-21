// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDefaultNamespaceOverrideSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Namespaces.lean
 */
contract PropertyDefaultNamespaceOverrideSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DefaultNamespaceOverrideSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: write has no unexpected revert
    function testAuto_Write_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("write(uint256)", uint256(1)));
        require(ok, "write reverted unexpectedly");
    }
}
