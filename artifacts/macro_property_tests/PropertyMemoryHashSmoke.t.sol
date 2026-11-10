// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMemoryHashSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/MemoryHashSmoke.lean
 */
contract PropertyMemoryHashSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("MemoryHashSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `hashBytes` result
    function testTODO_HashBytes_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("hashBytes(bytes)", hex"CAFE"));
        require(ok, "hashBytes reverted unexpectedly");
        assertEq(ret.length, 32, "hashBytes ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `hashWords` result
    function testTODO_HashWords_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("hashWords(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "hashWords reverted unexpectedly");
        assertEq(ret.length, 32, "hashWords ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
