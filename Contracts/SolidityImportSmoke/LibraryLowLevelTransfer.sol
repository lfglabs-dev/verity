// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A library function that sends native value or calls an ERC-20 `transfer` through inline
// assembly. It is lowered through its body like any other library function.

library CurrencyLibrary {
    error NativeTransferFailed();
    error ERC20TransferFailed();

    function transfer(address currency, address to, uint256 amount) internal {
        bool success;
        if (currency == address(0)) {
            assembly ("memory-safe") {
                success := call(gas(), to, amount, 0, 0, 0, 0)
            }
            if (!success) revert NativeTransferFailed();
        } else {
            assembly ("memory-safe") {
                let fmp := mload(0x40)
                mstore(fmp, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                mstore(add(fmp, 4), and(to, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(fmp, 36), amount)
                success :=
                    and(
                        or(and(eq(mload(0), 1), gt(returndatasize(), 31)), iszero(returndatasize())),
                        call(gas(), currency, 0, fmp, 68, 0, 32)
                    )
                mstore(fmp, 0)
                mstore(add(fmp, 0x20), 0)
                mstore(add(fmp, 0x40), 0)
            }
            if (!success) revert ERC20TransferFailed();
        }
    }
}

contract LibraryLowLevelTransfer {
    uint256 private first = 7;
    uint256 private second = 9;

    function pay(address currency, address to, uint256 amount) external {
        CurrencyLibrary.transfer(currency, to, amount);
    }
}
