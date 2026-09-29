// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDeferredBTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/LinkedGettersAndDeferred.lean
 */
contract PropertyDeferredBTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DeferredB");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: value reads storage slot 0 and decodes the result
    function testAuto_Value_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("value()"));
        require(ok, "value reverted unexpectedly");
        assertEq(ret.length, 32, "value ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "value should return storage slot 0");
    }
    // Property 2: TODO decode and assert `double` result
    function testTODO_Double_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("double()"));
        require(ok, "double reverted unexpectedly");
        assertEq(ret.length, 32, "double ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
