// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyAdtLinkedPayloadSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCallInBodySmoke.lean
 */
contract PropertyAdtLinkedPayloadSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("AdtLinkedPayloadSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: store has no unexpected revert
    function testAuto_Store_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("store()"));
        require(ok, "store reverted unexpectedly");
    }
}
