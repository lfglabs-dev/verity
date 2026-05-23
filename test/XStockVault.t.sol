// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "../examples/solidity/XStockVault.sol";

contract XStockVaultTest is Test {
    XStockVault vault;
    address token = address(0x1234);
    address user = address(0xBEEF);

    function setUp() public {
        vault = new XStockVault(token);
    }

    function testDepositMintsSharesAtCurrentEpoch() public {
        vm.prank(user);
        vault.deposit(10, 0);

        assertEq(vault.balanceOf(user), 10);
        assertEq(vault.totalAssets(), 10);
        assertEq(vault.totalSupply(), 10);
    }

    function testStaleEpochCannotDeposit() public {
        vault.updateMultiplierEpoch(2);

        vm.prank(user);
        vm.expectRevert(XStockVault.StaleMultiplierEpoch.selector);
        vault.deposit(10, 1);
    }

    function testPauseBlocksWithdraw() public {
        vm.prank(user);
        vault.deposit(10, 0);
        vault.setCorporateActionPaused(1);

        vm.prank(user);
        vm.expectRevert(XStockVault.CorporateActionWindow.selector);
        vault.withdraw(1, 0);
    }

    function testSyncUsesAdjustedBalanceDirectly() public {
        vault.syncFromBalanceOf(123);
        assertEq(vault.totalAssets(), 123);
    }

    function testDepositWithdrawRoundTrip(uint128 amount) public {
        vm.prank(user);
        vault.deposit(uint256(amount), 0);

        vm.prank(user);
        vault.withdraw(uint256(amount), 0);

        assertEq(vault.balanceOf(user), 0);
        assertEq(vault.totalAssets(), 0);
        assertEq(vault.totalSupply(), 0);
    }

    function testStaleEpochReverts(uint128 amount) public {
        vault.updateMultiplierEpoch(2);

        vm.prank(user);
        vm.expectRevert(XStockVault.StaleMultiplierEpoch.selector);
        vault.deposit(uint256(amount), 1);
    }
}
