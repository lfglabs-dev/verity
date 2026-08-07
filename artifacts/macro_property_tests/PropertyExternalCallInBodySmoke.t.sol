// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyExternalCallInBodySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCallInBodySmoke.lean
 */
contract PropertyExternalCallInBodySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ExternalCallInBodySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `linkedRead` result
    function testTODO_LinkedRead_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("linkedRead()"));
        require(ok, "linkedRead reverted unexpectedly");
        assertEq(ret.length, 32, "linkedRead ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: linkedWrite has no unexpected revert
    function testAuto_LinkedWrite_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("linkedWrite(uint256,bytes)", uint256(1), hex"CAFE"));
        require(ok, "linkedWrite reverted unexpectedly");
    }
}
