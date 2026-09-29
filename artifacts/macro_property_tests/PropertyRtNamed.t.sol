// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyRtNamedTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/LinkedRuntimeTarget.lean
 */
contract PropertyRtNamedTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("RtNamed");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `supplyOfY` result
    function testTODO_SupplyOfY_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("supplyOfY(address)", alice));
        require(ok, "supplyOfY reverted unexpectedly");
        assertEq(ret.length, 32, "supplyOfY ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
