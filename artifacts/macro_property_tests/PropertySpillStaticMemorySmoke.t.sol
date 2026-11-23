// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertySpillStaticMemorySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/SpillStaticMemorySmoke.lean
 */
contract PropertySpillStaticMemorySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("SpillStaticMemorySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: addChain decodes and matches the inferred straight-line result
    function testAuto_AddChain_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("addChain(uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1)));
        require(ok, "addChain reverted unexpectedly");
        assertEq(ret.length, 32, "addChain ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 32, "addChain should preserve the inferred result");
    }
    // Property 2: xorChain decodes and matches the inferred straight-line result
    function testAuto_XorChain_ReturnsInferredStraightLineResult() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("xorChain(uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1)));
        require(ok, "xorChain reverted unexpectedly");
        assertEq(ret.length, 32, "xorChain ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 0, "xorChain should preserve the inferred result");
    }
}
