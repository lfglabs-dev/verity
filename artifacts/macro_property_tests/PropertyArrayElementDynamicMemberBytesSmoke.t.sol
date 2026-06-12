// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyArrayElementDynamicMemberBytesSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ArrayElementDynamicMemberBytesSmoke.lean
 */
contract PropertyArrayElementDynamicMemberBytesSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ArrayElementDynamicMemberBytesSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `callDataLength` result
    function testTODO_CallDataLength_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("callDataLength((bytes,string))", abi.decode(abi.encode(hex"CAFE", "verity"), (bytes, string))));
        require(ok, "callDataLength reverted unexpectedly");
        assertEq(ret.length, 32, "callDataLength ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `labelLength` result
    function testTODO_LabelLength_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("labelLength((bytes,string))", abi.decode(abi.encode(hex"CAFE", "verity"), (bytes, string))));
        require(ok, "labelLength reverted unexpectedly");
        assertEq(ret.length, 32, "labelLength ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `getElmLength` result
    function testTODO_GetElmLength_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getElmLength((bytes,string)[],uint256)", abi.decode(abi.encode(uint256(0)), ((bytes,string)[])), uint256(1)));
        require(ok, "getElmLength reverted unexpectedly");
        assertEq(ret.length, 32, "getElmLength ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
