// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

/// @title XStockVault
/// @notice Minimal xStocks accounting skeleton with epoch-gated 1:1 shares.
/// @dev Matches `Contracts/XStockVault/XStockVault.lean`. Token transfers,
/// access control, and oracle authorization are deliberately out of scope for
/// this proof-of-concept and must be supplied by a production integration.
contract XStockVault {
    address public xStockToken;
    uint256 public totalAssets;
    uint256 public totalSupply;
    mapping(address => uint256) public shareBalances;
    uint256 public multiplierEpoch;
    uint256 public corporateActionPaused;

    error CorporateActionWindow();
    error StaleMultiplierEpoch();
    error InsufficientShares();
    error InsufficientAssets();
    error InsufficientSupply();
    error InvalidPauseFlag();

    constructor(address token) {
        xStockToken = token;
    }

    function setCorporateActionPaused(uint256 paused) external {
        if (paused != 0 && paused != 1) {
            revert InvalidPauseFlag();
        }
        corporateActionPaused = paused;
    }

    function updateMultiplierEpoch(uint256 newEpoch) external {
        multiplierEpoch = newEpoch;
    }

    function syncFromBalanceOf(uint256 adjustedBalanceOfVault) external {
        totalAssets = adjustedBalanceOfVault;
    }

    function deposit(uint256 assets, uint256 quoteEpoch) external {
        if (corporateActionPaused != 0) {
            revert CorporateActionWindow();
        }
        if (quoteEpoch != multiplierEpoch) {
            revert StaleMultiplierEpoch();
        }
        shareBalances[msg.sender] += assets;
        totalAssets += assets;
        totalSupply += assets;
    }

    function withdraw(uint256 shares, uint256 quoteEpoch) external {
        if (corporateActionPaused != 0) {
            revert CorporateActionWindow();
        }
        if (quoteEpoch != multiplierEpoch) {
            revert StaleMultiplierEpoch();
        }
        uint256 currentShares = shareBalances[msg.sender];
        if (currentShares < shares) {
            revert InsufficientShares();
        }
        if (totalAssets < shares) {
            revert InsufficientAssets();
        }
        if (totalSupply < shares) {
            revert InsufficientSupply();
        }
        shareBalances[msg.sender] = currentShares - shares;
        totalAssets -= shares;
        totalSupply -= shares;
    }

    function balanceOf(address account) external view returns (uint256) {
        return shareBalances[account];
    }
}
