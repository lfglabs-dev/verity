// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyQualifiedHelperLibraryTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/SecurityCombos.lean
 */
contract PropertyQualifiedHelperLibraryTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("QualifiedHelperLibrary");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: trustedEntry returns the direct parameter value
    function testAuto_TrustedEntry_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("trustedEntry(uint256)", uint256(1)));
        require(ok, "trustedEntry reverted unexpectedly");
        assertEq(ret.length, 32, "trustedEntry ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "trustedEntry should preserve the expected value");
    }
    // Property 2: trustedPair decodes and matches the inferred tuple result
    function testAuto_TrustedPair_ReturnsInferredTupleResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("trustedPair(uint256)", uint256(1)));
        require(ok, "trustedPair reverted unexpectedly");
        require(ret.length >= 64, "trustedPair ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, uint256(1), "trustedPair tuple element 0 should preserve the inferred result");
        assertEq(actual1, uint256(1), "trustedPair tuple element 1 should preserve the inferred result");
    }
    // Property 3: adversarialEntry returns the direct parameter value
    function testAuto_AdversarialEntry_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("adversarialEntry(uint256)", uint256(1)));
        require(ok, "adversarialEntry reverted unexpectedly");
        assertEq(ret.length, 32, "adversarialEntry ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "adversarialEntry should preserve the expected value");
    }
    // Property 4: adversarialPair decodes and matches the inferred tuple result
    function testAuto_AdversarialPair_ReturnsInferredTupleResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("adversarialPair(uint256)", uint256(1)));
        require(ok, "adversarialPair reverted unexpectedly");
        require(ret.length >= 64, "adversarialPair ABI tuple return payload unexpectedly short");
        (uint256 actual0, uint256 actual1) = abi.decode(ret, (uint256, uint256));
        assertEq(actual0, uint256(1), "adversarialPair tuple element 0 should preserve the inferred result");
        assertEq(actual1, uint256(1), "adversarialPair tuple element 1 should preserve the inferred result");
    }
}
