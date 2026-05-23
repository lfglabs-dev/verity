# Ink xStocks Research Notes

Prepared: 2026-05-23

These notes support the `XStockVault` Verity POC. The POC does not verify xStocks itself. It records the assumptions an Ink builder can use when proving their own vault, collateral adapter, wrapper, or strategy.

## Sources Checked

- xStocks docs introduction: https://docs.xstocks.fi/docs
- xStocks dividends and stock splits: https://docs.xstocks.fi/overview/dividends-and-stock-splits
- xStocks API reference: https://docs.xstocks.fi/apis/openapi
- Kraken xStocks FAQ: https://support.kraken.com/articles/xstocks-faq
- xStocks website: https://xstocks.fi/
- Ink explorer token page checked for TSLAx: https://explorer.inkonchain.com/token/0x8ad3c73f833d3f9a523ab01476625f269aeb7cf0

## Facts

- xStocks are tokenized representations of publicly traded equities and ETFs.
- xStocks documentation describes each token as 1:1 collateralized by the corresponding underlying equity or ETF.
- xStocks are available on Ethereum, Solana, Mantle, TON, Ink, and other EVM-compatible networks.
- The product is intended to be DeFi-composable: collateral, lending markets, liquidity pools, and structured products are named integration surfaces.
- Corporate actions such as dividends, stock splits, and reverse splits are reflected through an onchain rebasing mechanism called the multiplier.
- The multiplier tracks cumulative corporate-action effects over the token's life.
- On EVM chains, including Ink as an EVM-compatible chain, the docs say the smart contract adjusts balances automatically and `balanceOf()` returns the current equity-adjusted balance.
- Multiplier updates are published onchain before corporate events take effect. Activation is set for midnight UTC on the payable date, and protocols are advised to pause interactions briefly around activation.
- Kraken's FAQ says dividends are not paid as cash. Their economic benefit is reflected by a rebasing or multiplier mechanism.
- The public xStocks API exposes asset metadata, contract addresses, current multiplier values, and multiplier history. A TSLAx API lookup returned the Ink deployment `0x8ad3c73f833d3f9a523ab01476625f269aeb7cf0`.

## Assumptions

- The POC treats Ink as an EVM integration for the purpose of `balanceOf()` behavior.
- The POC assumes the xStock token contract's `balanceOf(vault)` result is already adjusted for the current multiplier.
- The POC assumes a corporate-action epoch changes whenever a multiplier update becomes relevant to vault quotes or settlement.
- The POC assumes transfer success or failure is handled by a surrounding integration layer. It does not prove token transfer internals.
- The POC does not prove source verification status for Ink xStock contracts. The API confirms deployment metadata; if a production proof needs bytecode-level assumptions, the next step is to compare Ink bytecode and ABI against verified EVM deployments.

## Integration Hazards

- Treating EVM `balanceOf()` as a raw token amount and multiplying it by the xStocks multiplier again.
- Double-counting a dividend, split, or reverse split in cached accounting.
- Minting shares from an old quote after a multiplier epoch has changed.
- Settling deposits or withdrawals during the recommended pause window around a multiplier activation timestamp.
- Using stale reference prices or stale multiplier values in collateral valuation.
- Mixing xStock amounts, USD values, decimals, and vault shares without explicit conversion boundaries.
- Letting a collateral adapter borrow against inflated or stale xStock values.
- Reminting or burning vault shares during corporate actions in a way that transfers value between users.

## Why The Three POC Invariants Are xStocks-Specific

1. EVM `balanceOf()` must be used exactly once because xStocks hide corporate-action adjustment inside the standard ERC-20 balance surface on EVM chains.
2. Corporate-action multiplier updates should scale each user's claim without changing share fractions. Normal ERC-20 vaults do not have automatic equity rebases from dividends, splits, or reverse splits.
3. Deposit and withdrawal quotes must be invalidated across multiplier epochs because xStocks publish scheduled corporate-action state changes that can alter adjusted balances between quote and settlement.

## Open Follow-Up

- Confirm whether each Ink xStock token has verified source in Blockscout and record ABI, proxy, and implementation details.
- Compare TSLAx, AAPLx, NVDAx, and SPYx deployment metadata from the public API.
- Decide whether a future production kit should model transfer restrictions or paused token states.
