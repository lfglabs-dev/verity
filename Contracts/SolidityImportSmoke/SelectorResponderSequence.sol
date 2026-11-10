// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IQuoted {
    function quote(uint256 x) external view returns (uint256);
    function pay(address to, uint256 amount) external returns (bool);
    function ping(uint256 x) external;
}

/// Three kinds of typed external call to one account: a `view` function (a `staticcall`
/// returning one word), a `nonpayable` function returning a `bool`, and one returning
/// nothing. Their selectors differ, so a selector-dispatched responder answers each with its
/// own entry. State is written before each call, so every call is a trailing interaction.
contract SelectorResponderFixture {
    uint256 private asked;
    uint256 private paid;
    uint256 private pings;

    function ask(address target, uint256 x) external returns (uint256) {
        asked += 1;
        uint256 quoted = IQuoted(target).quote(x);
        return quoted;
    }

    function settle(address target, address to, uint256 amount) external {
        paid += amount;
        require(IQuoted(target).pay(to, amount), "pay");
    }

    function poke(address target, uint256 x) external {
        pings += 1;
        IQuoted(target).ping(x);
    }

    function read() external view returns (uint256, uint256, uint256) {
        return (asked, paid, pings);
    }
}
