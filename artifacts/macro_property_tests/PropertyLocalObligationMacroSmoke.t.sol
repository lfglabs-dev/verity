// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyLocalObligationMacroSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/LocalObligationMacroSmoke/LocalObligationMacroSmoke.lean
 */
contract PropertyLocalObligationMacroSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("LocalObligationMacroSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: unsafeEdge has no unexpected revert
    function testAuto_UnsafeEdge_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("unsafeEdge()"));
        require(ok, "unsafeEdge reverted unexpectedly");
    }
    // Property 2: dischargedEdge decodes and matches the inferred straight-line result
    function testAuto_DischargedEdge_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("dischargedEdge(uint256)", uint256(1)));
        require(ok, "dischargedEdge reverted unexpectedly");
        assertEq(ret.length, 32, "dischargedEdge ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "dischargedEdge should preserve the inferred result");
    }
}
