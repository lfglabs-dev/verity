// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyZeroAddressShadowSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyZeroAddressShadowSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ZeroAddressShadowSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: shadowWrite has no unexpected revert
    function testAuto_ShadowWrite_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("shadowWrite(address)", alice));
        require(ok, "shadowWrite reverted unexpectedly");
    }
}
