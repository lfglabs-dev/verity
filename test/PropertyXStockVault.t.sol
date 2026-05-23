// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "../examples/solidity/XStockVault.sol";

contract PropertyXStockVaultTest is Test {
    XStockVault vault;
    address user = address(0xBEEF);

    function setUp() public {
        vault = new XStockVault(address(0x1234));
    }

    /// Property 1: totalAssets_spec_reads_slot_one
    /// Property 2: syncFromBalanceOf_sets_assets_to_adjusted_balance
    /// Property 3: sync_uses_evm_adjusted_balance_exactly_once
    /// Property 4: syncFromBalanceOf_preserves_unrelated_storage
    function testProperty_SyncFromBalanceOf_UsesAdjustedBalanceDirectly(uint256 adjustedBalance) public {
        vm.prank(user);
        vault.deposit(7, 0);
        vault.updateMultiplierEpoch(3);
        vault.setCorporateActionPaused(1);

        uint256 supplyBefore = vault.totalSupply();
        uint256 sharesBefore = vault.balanceOf(user);
        uint256 epochBefore = vault.multiplierEpoch();
        uint256 pauseBefore = vault.corporateActionPaused();
        address tokenBefore = vault.xStockToken();

        vault.syncFromBalanceOf(adjustedBalance);

        assertEq(vault.totalAssets(), adjustedBalance);
        assertEq(vault.totalSupply(), supplyBefore);
        assertEq(vault.balanceOf(user), sharesBefore);
        assertEq(vault.multiplierEpoch(), epochBefore);
        assertEq(vault.corporateActionPaused(), pauseBefore);
        assertEq(vault.xStockToken(), tokenBefore);
    }

    /// Property 5: totalSupply_spec_reads_slot_two
    /// Property 6: deposit_spec_preserves_multiplier_epoch
    /// Property 7: deposit_spec_preserves_pause_flag
    function testProperty_DepositUpdatesSupply(uint128 amount) public {
        vault.updateMultiplierEpoch(9);
        uint256 pauseBefore = vault.corporateActionPaused();

        vm.prank(user);
        vault.deposit(uint256(amount), 9);

        assertEq(vault.totalSupply(), uint256(amount));
        assertEq(vault.multiplierEpoch(), 9);
        assertEq(vault.corporateActionPaused(), pauseBefore);
    }

    /// Property 8: multiplierEpoch_spec_reads_slot_four
    function testProperty_MultiplierEpochReadsSlot(uint256 epoch) public {
        vault.updateMultiplierEpoch(epoch);
        assertEq(vault.multiplierEpoch(), epoch);
    }

    /// Property 9: stale_epoch_deposit_spec_impossible
    /// Property 10: stale_multiplier_epoch_cannot_settle_deposit
    function testProperty_StaleEpochCannotDeposit(uint128 amount, uint256 currentEpoch, uint256 staleEpoch) public {
        vm.assume(staleEpoch != currentEpoch);
        vault.updateMultiplierEpoch(currentEpoch);

        vm.prank(user);
        vm.expectRevert(XStockVault.StaleMultiplierEpoch.selector);
        vault.deposit(uint256(amount), staleEpoch);
    }

    /// Property 11: corporate_action_preserves_fraction_and_scales_claim
    function testProperty_EpochUpdateDoesNotRemintShares(uint128 amount, uint256 newEpoch) public {
        vm.prank(user);
        vault.deposit(uint256(amount), 0);
        uint256 sharesBefore = vault.balanceOf(user);
        uint256 supplyBefore = vault.totalSupply();

        vault.updateMultiplierEpoch(newEpoch);

        assertEq(vault.balanceOf(user), sharesBefore);
        assertEq(vault.totalSupply(), supplyBefore);
    }

    /// Property 12: withdraw_spec_preserves_multiplier_epoch
    /// Property 13: withdraw_spec_preserves_pause_flag
    function testProperty_WithdrawPreservesEpochAndPause(uint128 amount) public {
        vault.updateMultiplierEpoch(11);

        vm.prank(user);
        vault.deposit(uint256(amount), 11);

        uint256 epochBefore = vault.multiplierEpoch();
        uint256 pauseBefore = vault.corporateActionPaused();

        vm.prank(user);
        vault.withdraw(uint256(amount), 11);

        assertEq(vault.multiplierEpoch(), epochBefore);
        assertEq(vault.corporateActionPaused(), pauseBefore);
    }
}
