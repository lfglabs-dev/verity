// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyCallResultSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCalls.lean
 */
contract PropertyCallResultSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("CallResultSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: storeCallResult has no unexpected revert
    function testAuto_StoreCallResult_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("storeCallResult(uint256)", uint256(1)));
        require(ok, "storeCallResult reverted unexpectedly");
    }
}
