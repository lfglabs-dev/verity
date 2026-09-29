// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDefVaultTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/LinkedRuntimeTarget.lean
 */
contract PropertyDefVaultTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DefVault");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `mintAndSupply` result
    function testTODO_MintAndSupply_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("mintAndSupply(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "mintAndSupply reverted unexpectedly");
        assertEq(ret.length, 32, "mintAndSupply ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: burnFrom has no unexpected revert
    function testAuto_BurnFrom_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("burnFrom(address,uint256)", alice, uint256(1)));
        require(ok, "burnFrom reverted unexpectedly");
    }
}
