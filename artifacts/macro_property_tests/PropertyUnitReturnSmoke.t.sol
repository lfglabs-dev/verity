// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyUnitReturnSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/UnitReturnSmoke.lean
 */
contract PropertyUnitReturnSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("UnitReturnSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: bumpTwice has no unexpected revert
    function testAuto_BumpTwice_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("bumpTwice(uint256)", uint256(1)));
        require(ok, "bumpTwice reverted unexpectedly");
    }
    // Property 2: hitsAndAfter decodes and matches the inferred tuple result
    function testAuto_HitsAndAfter_ReturnsInferredTupleResult() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        uint256 expected1 = uint256(1);
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(expected1)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("hitsAndAfter()"));
        require(ok, "hitsAndAfter reverted unexpectedly");
        require(ret.length >= 64, "hitsAndAfter ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, expected, "hitsAndAfter tuple element 0 should preserve the inferred result");
        assertEq(actual1, expected1, "hitsAndAfter tuple element 1 should preserve the inferred result");
    }
}
