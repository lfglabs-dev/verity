// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNonreentrantQualifiedHelperResolutionTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/SecurityCombos.lean
 */
contract PropertyNonreentrantQualifiedHelperResolutionTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("NonreentrantQualifiedHelperResolution");
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
    // Property 3: TODO decode and assert `adversarialEntry` result
    function testTODO_AdversarialEntry_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("adversarialEntry(uint256)", uint256(1)));
        require(ok, "adversarialEntry reverted unexpectedly");
        assertEq(ret.length, 32, "adversarialEntry ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `adversarialPair` result
    function testTODO_AdversarialPair_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("adversarialPair(uint256)", uint256(1)));
        require(ok, "adversarialPair reverted unexpectedly");
        require(ret.length >= 64, "adversarialPair ABI tuple return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: overloadedTrusted returns the declared constant result
    function testAuto_OverloadedTrusted_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("overloadedTrusted(address)", alice));
        require(ok, "overloadedTrusted reverted unexpectedly");
        assertEq(ret.length, 32, "overloadedTrusted ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 0, "overloadedTrusted should return the declared constant");
    }
    // Property 6: overloadedTrusted returns the direct parameter value
    function testAuto_OverloadedTrusted_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("overloadedTrusted(uint256)", uint256(1)));
        require(ok, "overloadedTrusted reverted unexpectedly");
        assertEq(ret.length, 32, "overloadedTrusted ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "overloadedTrusted should preserve the expected value");
    }
    // Property 7: overloadedAdversarial returns the declared constant result
    function testAuto_OverloadedAdversarial_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("overloadedAdversarial(address)", alice));
        require(ok, "overloadedAdversarial reverted unexpectedly");
        assertEq(ret.length, 32, "overloadedAdversarial ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 0, "overloadedAdversarial should return the declared constant");
    }
    // Property 8: TODO decode and assert `overloadedAdversarial` result
    function testTODO_OverloadedAdversarial_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("overloadedAdversarial(uint256)", uint256(1)));
        require(ok, "overloadedAdversarial reverted unexpectedly");
        assertEq(ret.length, 32, "overloadedAdversarial ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 9: TODO decode and assert `qualifiedSpace` result
    function testTODO_QualifiedSpace_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("qualifiedSpace(uint256)", uint256(1)));
        require(ok, "qualifiedSpace reverted unexpectedly");
        assertEq(ret.length, 32, "qualifiedSpace ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 10: TODO decode and assert `qualifiedDestructure` result
    function testTODO_QualifiedDestructure_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("qualifiedDestructure(uint256)", uint256(1)));
        require(ok, "qualifiedDestructure reverted unexpectedly");
        assertEq(ret.length, 32, "qualifiedDestructure ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 11: TODO decode and assert `qualifiedAdversarialSpace` result
    function testTODO_QualifiedAdversarialSpace_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("qualifiedAdversarialSpace(uint256)", uint256(1)));
        require(ok, "qualifiedAdversarialSpace reverted unexpectedly");
        assertEq(ret.length, 32, "qualifiedAdversarialSpace ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 12: TODO decode and assert `qualifiedAdversarialDestructure` result
    function testTODO_QualifiedAdversarialDestructure_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("qualifiedAdversarialDestructure(uint256)", uint256(1)));
        require(ok, "qualifiedAdversarialDestructure reverted unexpectedly");
        assertEq(ret.length, 32, "qualifiedAdversarialDestructure ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 13: overloadedTrustedCaller has no unexpected revert
    function testAuto_OverloadedTrustedCaller_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("overloadedTrustedCaller(uint256)", uint256(1)));
        require(ok, "overloadedTrustedCaller reverted unexpectedly");
    }
    // Property 14: overloadedAdversarialCaller has no unexpected revert
    function testAuto_OverloadedAdversarialCaller_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("overloadedAdversarialCaller(uint256)", uint256(1)));
        require(ok, "overloadedAdversarialCaller reverted unexpectedly");
    }
    // Property 15: overloadedTrustedLocalCaller has no unexpected revert
    function testAuto_OverloadedTrustedLocalCaller_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("overloadedTrustedLocalCaller()"));
        require(ok, "overloadedTrustedLocalCaller reverted unexpectedly");
    }
    // Property 16: overloadedAdversarialLocalCaller has no unexpected revert
    function testAuto_OverloadedAdversarialLocalCaller_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("overloadedAdversarialLocalCaller()"));
        require(ok, "overloadedAdversarialLocalCaller reverted unexpectedly");
    }
}
