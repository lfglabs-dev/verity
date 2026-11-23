// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyEventCompositeLiteralSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/EventCompositeLiteralSmoke.lean
 */
contract PropertyEventCompositeLiteralSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("EventCompositeLiteralSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: cutOne has no unexpected revert
    function testAuto_CutOne_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("cutOne(uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1)));
        require(ok, "cutOne reverted unexpectedly");
    }
    // Property 2: pair has no unexpected revert
    function testAuto_Pair_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pair(uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1)));
        require(ok, "pair reverted unexpectedly");
    }
}
