// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyBitmapIteratorSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Intrinsics.lean
 */
contract PropertyBitmapIteratorSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("BitmapIteratorSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `leadingZeros` result
    function testTODO_LeadingZeros_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("leadingZeros(uint256)", uint256(1)));
        require(ok, "leadingZeros reverted unexpectedly");
        assertEq(ret.length, 32, "leadingZeros ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `mostSignificantBit` result
    function testTODO_MostSignificantBit_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("mostSignificantBit(uint256)", uint256(1)));
        require(ok, "mostSignificantBit reverted unexpectedly");
        assertEq(ret.length, 32, "mostSignificantBit ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: rememberSetBits has no unexpected revert
    function testAuto_RememberSetBits_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("rememberSetBits(uint256)", uint256(1)));
        require(ok, "rememberSetBits reverted unexpectedly");
    }
}
