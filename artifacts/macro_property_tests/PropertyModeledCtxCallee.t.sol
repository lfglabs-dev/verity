// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyModeledCtxCalleeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ModeledCallCtx.lean
 */
contract PropertyModeledCtxCalleeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ModeledCtxCallee");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: poke has no unexpected revert
    function testAuto_Poke_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("poke(address,uint256)", alice, uint256(1)));
        require(ok, "poke reverted unexpectedly");
    }
}
