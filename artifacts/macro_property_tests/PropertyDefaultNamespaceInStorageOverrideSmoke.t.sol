// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDefaultNamespaceInStorageOverrideSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyDefaultNamespaceInStorageOverrideSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DefaultNamespaceInStorageOverrideSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: writeRoot has no unexpected revert
    function testAuto_WriteRoot_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("writeRoot(uint256)", uint256(1)));
        require(ok, "writeRoot reverted unexpectedly");
    }
}
