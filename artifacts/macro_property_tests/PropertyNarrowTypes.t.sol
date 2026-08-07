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
    // Property 2: echoUint96 returns the direct parameter value
    function testAuto_EchoUint96_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoUint96(uint96)", uint96(1)));
        require(ok, "echoUint96 reverted unexpectedly");
        assertEq(ret.length, 32, "echoUint96 ABI return length mismatch (expected 32 bytes)");
        uint96 actual = abi.decode(ret, (uint96));
        assertEq(actual, uint96(1), "echoUint96 should preserve the expected value");
    }
    // Property 3: echoInt64 returns the direct parameter value
    function testAuto_EchoInt64_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoInt64(int64)", int64(1)));
        require(ok, "echoInt64 reverted unexpectedly");
        assertEq(ret.length, 32, "echoInt64 ABI return length mismatch (expected 32 bytes)");
        int64 actual = abi.decode(ret, (int64));
        assertEq(actual, int64(1), "echoInt64 should preserve the expected value");
    }
    // Property 4: echoBytes4 returns the direct parameter value
    function testAuto_EchoBytes4_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoBytes4(bytes4)", bytes4(uint32(0x01))));
        require(ok, "echoBytes4 reverted unexpectedly");
        assertEq(ret.length, 32, "echoBytes4 ABI return length mismatch (expected 32 bytes)");
        bytes4 actual = abi.decode(ret, (bytes4));
        assertEq(actual, bytes4(uint32(0x01)), "echoBytes4 should preserve the expected value");
    }
    // Property 5: echoBytes20 returns the direct parameter value
    function testAuto_EchoBytes20_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoBytes20(bytes20)", bytes20(uint160(0x01))));
        require(ok, "echoBytes20 reverted unexpectedly");
        assertEq(ret.length, 32, "echoBytes20 ABI return length mismatch (expected 32 bytes)");
        bytes20 actual = abi.decode(ret, (bytes20));
        assertEq(actual, bytes20(uint160(0x01)), "echoBytes20 should preserve the expected value");
    }
    // Property 6: TODO decode and assert `wrappingAddUint128` result
    function testTODO_WrappingAddUint128_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("wrappingAddUint128(uint128,uint128)", uint128(1), uint128(1)));
        require(ok, "wrappingAddUint128 reverted unexpectedly");
        assertEq(ret.length, 32, "wrappingAddUint128 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 7: TODO decode and assert `wrappingSubUint128` result
    function testTODO_WrappingSubUint128_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("wrappingSubUint128(uint128,uint128)", uint128(1), uint128(1)));
        require(ok, "wrappingSubUint128 reverted unexpectedly");
        assertEq(ret.length, 32, "wrappingSubUint128 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 8: TODO decode and assert `wrappingMulUint128` result
    function testTODO_WrappingMulUint128_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("wrappingMulUint128(uint128,uint128)", uint128(1), uint128(1)));
        require(ok, "wrappingMulUint128 reverted unexpectedly");
        assertEq(ret.length, 32, "wrappingMulUint128 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 9: TODO decode and assert `mulUint248` result
    function testTODO_MulUint248_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("mulUint248(uint248,uint248)", uint248(1), uint248(1)));
        require(ok, "mulUint248 reverted unexpectedly");
        assertEq(ret.length, 32, "mulUint248 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 10: TODO decode and assert `castUint128` result
    function testTODO_CastUint128_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castUint128(uint256)", uint256(1)));
        require(ok, "castUint128 reverted unexpectedly");
        assertEq(ret.length, 32, "castUint128 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 11: TODO decode and assert `castInt64` result
    function testTODO_CastInt64_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castInt64(uint256)", uint256(1)));
        require(ok, "castInt64 reverted unexpectedly");
        assertEq(ret.length, 32, "castInt64 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 12: TODO decode and assert `castBytes20` result
    function testTODO_CastBytes20_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castBytes20(uint256)", uint256(1)));
        require(ok, "castBytes20 reverted unexpectedly");
        assertEq(ret.length, 32, "castBytes20 ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Narrow scalar boundary and dirty-word regressions execute deployed generated Yul.
    function testBoundary_NarrowTypes() public {
        (bool okNeg, bytes memory negRet) = target.call(
            abi.encodeWithSignature("echoInt64(int64)", type(int64).min));
        require(okNeg, "negative int64 reverted");
        assertEq(abi.decode(negRet, (int64)), type(int64).min);

        (bool okAdd, bytes memory addRet) = target.call(
            abi.encodeWithSignature("wrappingAddUint128(uint128,uint128)", type(uint128).max, uint128(1)));
        require(okAdd, "wrapping add reverted");
        assertEq(abi.decode(addRet, (uint128)), uint128(0));

        (bool okSub, bytes memory subRet) = target.call(
            abi.encodeWithSignature("wrappingSubUint128(uint128,uint128)", uint128(0), uint128(1)));
        require(okSub, "wrapping sub reverted");
        assertEq(abi.decode(subRet, (uint128)), type(uint128).max);

        (bool okMul, bytes memory mulRet) = target.call(
            abi.encodeWithSignature("wrappingMulUint128(uint128,uint128)", type(uint128).max, uint128(2)));
        require(okMul, "wrapping mul reverted");
        assertEq(abi.decode(mulRet, (uint128)), type(uint128).max - 1);
    }

    function testMalformed_NarrowCalldataCanonicalized() public {
        bytes4 uintSelector = bytes4(keccak256("echoUint128(uint128)"));
        (bool okUint, bytes memory uintRet) = target.call(
            abi.encodePacked(uintSelector, bytes32(type(uint256).max)));
        require(okUint, "dirty uint128 calldata reverted");
        assertEq(abi.decode(uintRet, (uint128)), type(uint128).max);

        bytes4 bytesSelector = bytes4(keccak256("echoBytes4(bytes4)"));
        bytes32 dirtyBytes4 = bytes32((uint256(0xdeadbeef) << 224) | 0x1234);
        (bool okBytes, bytes memory bytesRet) = target.call(
            abi.encodePacked(bytesSelector, dirtyBytes4));
        require(okBytes, "dirty bytes4 calldata reverted");
        assertEq(abi.decode(bytesRet, (bytes4)), bytes4(0xdeadbeef));
    }
}
