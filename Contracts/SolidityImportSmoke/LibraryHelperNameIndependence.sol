// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// An internal library function is modeled by its own body, whatever the library and function
// are called. `CurrencyLibrary.transfer` with three arguments once selected a fixed native or
// ERC-20 CALL lowering in place of the body.

library CurrencyLibrary {
    function transfer(address currency, address to, uint256 amount) internal pure {
        require(to != address(0));
        require(amount <= 1000 || currency == address(0));
    }
}

library AmountGuard {
    function check(address currency, address to, uint256 amount) internal pure {
        require(to != address(0));
        require(amount <= 1000 || currency == address(0));
    }
}

// The same body under two library and function names: both must import, and agree with solc.
contract LibraryHelperNameIndependence {
    uint256 private first = 7;
    uint256 private second = 9;

    function viaCurrencyName(address currency, address to, uint256 amount) external pure returns (uint256) {
        CurrencyLibrary.transfer(currency, to, amount);
        return amount * 2;
    }

    function viaOtherName(address currency, address to, uint256 amount) external pure returns (uint256) {
        AmountGuard.check(currency, to, amount);
        return amount * 2;
    }
}
