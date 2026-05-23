// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyXStockVaultTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/XStockVault/XStockVault.lean
 */
contract PropertyXStockVaultTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("XStockVault", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setCorporateActionPaused has no unexpected revert
    function testAuto_SetCorporateActionPaused_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setCorporateActionPaused(uint256)", uint256(1)));
        require(ok, "setCorporateActionPaused reverted unexpectedly");
    }
    // Property 2: updateMultiplierEpoch has no unexpected revert
    function testAuto_UpdateMultiplierEpoch_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("updateMultiplierEpoch(uint256)", uint256(1)));
        require(ok, "updateMultiplierEpoch reverted unexpectedly");
    }
    // Property 3: syncFromBalanceOf has no unexpected revert
    function testAuto_SyncFromBalanceOf_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("syncFromBalanceOf(uint256)", uint256(1)));
        require(ok, "syncFromBalanceOf reverted unexpectedly");
    }
    // Property 4: deposit has no unexpected revert
    function testAuto_Deposit_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("deposit(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "deposit reverted unexpectedly");
    }
    // Property 5: withdraw has no unexpected revert
    function testAuto_Withdraw_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("withdraw(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "withdraw reverted unexpectedly");
    }
    // Property 6: balanceOf reads the configured mapping value
    function testAuto_BalanceOf_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 3), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(ok, "balanceOf reverted unexpectedly");
        assertEq(ret.length, 32, "balanceOf ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "balanceOf should decode the configured mapping value");
    }
    // Property 7: totalAssets reads storage slot 1 and decodes the result
    function testAuto_TotalAssets_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalAssets()"));
        require(ok, "totalAssets reverted unexpectedly");
        assertEq(ret.length, 32, "totalAssets ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "totalAssets should return storage slot 1");
    }
    // Property 8: totalSupply reads storage slot 2 and decodes the result
    function testAuto_TotalSupply_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(2)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("totalSupply()"));
        require(ok, "totalSupply reverted unexpectedly");
        assertEq(ret.length, 32, "totalSupply ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "totalSupply should return storage slot 2");
    }
    // Property 9: multiplierEpoch reads storage slot 4 and decodes the result
    function testAuto_MultiplierEpoch_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(4)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("multiplierEpoch()"));
        require(ok, "multiplierEpoch reverted unexpectedly");
        assertEq(ret.length, 32, "multiplierEpoch ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "multiplierEpoch should return storage slot 4");
    }
}
