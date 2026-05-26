// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyIntrinsicClzSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke.lean
 */
contract PropertyIntrinsicClzSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("IntrinsicClzSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `countLeadingZeros` result
    function testTODO_CountLeadingZeros_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("countLeadingZeros(uint256)", uint256(1)));
        require(ok, "countLeadingZeros reverted unexpectedly");
        assertEq(ret.length, 32, "countLeadingZeros ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
