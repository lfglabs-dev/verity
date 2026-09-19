// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyTryCatchArgSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/TryCatch.lean
 */
contract PropertyTryCatchArgSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("TryCatchArgSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: hopWithArg has no unexpected revert
    function testAuto_HopWithArg_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("hopWithArg(uint256)", uint256(1)));
        require(ok, "hopWithArg reverted unexpectedly");
    }
    // Property 2: hopWithCall has no unexpected revert
    function testAuto_HopWithCall_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("hopWithCall(address,uint256)", alice, uint256(1)));
        require(ok, "hopWithCall reverted unexpectedly");
    }
}
