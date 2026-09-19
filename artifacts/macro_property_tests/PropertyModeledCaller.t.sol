// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyModeledCallerTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ModeledCall.lean
 */
contract PropertyModeledCallerTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ModeledCaller");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `record` result
    function testTODO_Record_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("record(address)", alice));
        require(ok, "record reverted unexpectedly");
        assertEq(ret.length, 32, "record ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: ping has no unexpected revert
    function testAuto_Ping_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("ping(address,uint256)", alice, uint256(1)));
        require(ok, "ping reverted unexpectedly");
    }
}
