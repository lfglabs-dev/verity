// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectDynamicECMArgSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCalls.lean
 */
contract PropertyDirectDynamicECMArgSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectDynamicECMArgSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `fromCall` result
    function testTODO_FromCall_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("fromCall(bytes)", hex"CAFE"));
        require(ok, "fromCall reverted unexpectedly");
        assertEq(ret.length, 32, "fromCall ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: fromDo has no unexpected revert
    function testAuto_FromDo_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("fromDo(string)", "verity"));
        require(ok, "fromDo reverted unexpectedly");
    }
    // Property 3: fromBind has no unexpected revert
    function testAuto_FromBind_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("fromBind(uint256[])", _singletonUintArray(1)));
        require(ok, "fromBind reverted unexpectedly");
    }

    function _singletonUintArray(uint256 x) internal pure returns (uint256[] memory arr) {
        arr = new uint256[](1);
        arr[0] = x;
    }
}
