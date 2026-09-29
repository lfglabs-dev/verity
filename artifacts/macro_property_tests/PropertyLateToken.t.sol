// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyLateTokenTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/LinkedRuntimeTarget.lean
 */
contract PropertyLateTokenTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("LateToken");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: mint has no unexpected revert
    function testAuto_Mint_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("mint(address,uint256)", alice, uint256(1)));
        require(ok, "mint reverted unexpectedly");
    }
    // Property 2: burn has no unexpected revert
    function testAuto_Burn_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("burn(uint256)", uint256(1)));
        require(ok, "burn reverted unexpectedly");
    }
    // Property 3: totalSupply reads storage slot 0 and decodes the result
    function testAuto_TotalSupply_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalSupply()"));
        require(ok, "totalSupply reverted unexpectedly");
        assertEq(ret.length, 32, "totalSupply ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "totalSupply should return storage slot 0");
    }
}
