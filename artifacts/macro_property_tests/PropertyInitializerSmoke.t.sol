// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyInitializerSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Declarations.lean
 */
contract PropertyInitializerSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("InitializerSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: initOwner has no unexpected revert
    function testAuto_InitOwner_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("initOwner(address)", alice));
        require(ok, "initOwner reverted unexpectedly");
    }
    // Property 2: upgradeToV2 has no unexpected revert
    function testAuto_UpgradeToV2_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("upgradeToV2()"));
        require(ok, "upgradeToV2 reverted unexpectedly");
    }
}
