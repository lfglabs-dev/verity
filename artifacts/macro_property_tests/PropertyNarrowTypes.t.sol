// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNarrowTypesTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Examples/NarrowTypes.lean
 */
contract PropertyNarrowTypesTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("NarrowTypes");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echoUint128 returns the direct parameter value
    function testAuto_EchoUint128_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoUint128(uint128)", uint128(1)));
        require(ok, "echoUint128 reverted unexpectedly");
        assertEq(ret.length, 32, "echoUint128 ABI return length mismatch (expected 32 bytes)");
        uint128 actual = abi.decode(ret, (uint128));
        assertEq(actual, uint128(1), "echoUint128 should preserve the expected value");
    }
    // Property 2: echoInt64 returns the direct parameter value
    function testAuto_EchoInt64_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoInt64(int64)", int64(1)));
        require(ok, "echoInt64 reverted unexpectedly");
        assertEq(ret.length, 32, "echoInt64 ABI return length mismatch (expected 32 bytes)");
        int64 actual = abi.decode(ret, (int64));
        assertEq(actual, int64(1), "echoInt64 should preserve the expected value");
    }
    // Property 3: echoBytes20 returns the direct parameter value
    function testAuto_EchoBytes20_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoBytes20(bytes20)", bytes20(uint160(0xBEEF))));
        require(ok, "echoBytes20 reverted unexpectedly");
        assertEq(ret.length, 32, "echoBytes20 ABI return length mismatch (expected 32 bytes)");
        bytes20 actual = abi.decode(ret, (bytes20));
        assertEq(actual, bytes20(uint160(0xBEEF)), "echoBytes20 should preserve the expected value");
    }
    // Property 4: TODO decode and assert `castUint128` result
    function testTODO_CastUint128_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castUint128(uint256)", uint256(1)));
        require(ok, "castUint128 reverted unexpectedly");
        assertEq(ret.length, 32, "castUint128 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `castInt64` result
    function testTODO_CastInt64_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castInt64(uint256)", uint256(1)));
        require(ok, "castInt64 reverted unexpectedly");
        assertEq(ret.length, 32, "castInt64 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 6: TODO decode and assert `castBytes20` result
    function testTODO_CastBytes20_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castBytes20(uint256)", uint256(1)));
        require(ok, "castBytes20 reverted unexpectedly");
        assertEq(ret.length, 32, "castBytes20 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
