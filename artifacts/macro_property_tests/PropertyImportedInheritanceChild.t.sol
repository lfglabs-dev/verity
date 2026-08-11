// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyImportedInheritanceChildTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/InheritanceImportChild.lean
 */
contract PropertyImportedInheritanceChildTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ImportedInheritanceChild");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setImported has no unexpected revert
    function testAuto_SetImported_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setImported(uint256)", uint256(1)));
        require(ok, "setImported reverted unexpectedly");
    }
}
