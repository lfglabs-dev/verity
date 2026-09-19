// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyModeledCtxInnerTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ModeledCallCtx.lean
 */
contract PropertyModeledCtxInnerTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ModeledCtxInner");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: set has no unexpected revert
    function testAuto_Set_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("set(uint256)", uint256(1)));
        require(ok, "set reverted unexpectedly");
    }
}
