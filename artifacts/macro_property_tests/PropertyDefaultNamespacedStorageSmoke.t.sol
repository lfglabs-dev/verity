// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDefaultNamespacedStorageSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyDefaultNamespacedStorageSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DefaultNamespacedStorageSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: write has no unexpected revert
    function testAuto_Write_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("write(uint256,address)", uint256(1), alice));
        require(ok, "write reverted unexpectedly");
    }
}
