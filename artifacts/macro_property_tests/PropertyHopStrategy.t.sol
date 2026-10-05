// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyHopStrategyTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Erc20BalanceHop.lean
 */
contract PropertyHopStrategyTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("HopStrategy");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `held` result
    function testTODO_Held_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("held(address,address)", alice, alice));
        require(ok, "held reverted unexpectedly");
        assertEq(ret.length, 32, "held ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: pay has no unexpected revert
    function testAuto_Pay_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pay(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "pay reverted unexpectedly");
    }
}
