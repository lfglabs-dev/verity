// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IWordOracle {
    enum Mode { Call, DelegateCall, Static }

    function allowed(address account) external view returns (bool);
    function quote(uint256 amount, bytes32 tag) external view returns (uint256);
    function tagOf(address account, bool flag) external view returns (bytes32);
    function quoteMode(uint256 amount, Mode mode) external view returns (uint256);
}

contract InterfaceWordStaticCallFixture {
    error Gated(uint256 code);

    uint256 private saved;
    bytes32 private label;

    function check(address oracle, address account) external view returns (bool) {
        bool ok = IWordOracle(oracle).allowed(account);
        return ok;
    }

    function gated(address oracle, uint256 next) external returns (uint256) {
        require(oracle == address(0) || IWordOracle(oracle).allowed(msg.sender), Gated(next));
        saved = next;
        return next;
    }

    function both(address oracle, address account, uint256 next) external returns (uint256) {
        saved = next;
        bool ok = next % 2 == 0 && IWordOracle(oracle).allowed(account);
        if (!ok) revert Gated(next);
        return next;
    }

    function price(address oracle, uint256 amount, bytes32 tag) external returns (uint256) {
        saved = amount;
        uint256 value;
        value = IWordOracle(oracle).quote(amount, tag);
        IWordOracle(oracle).quote(7, tag);
        return value;
    }

    function stamp(address oracle, address account, bool flag) external returns (bytes32) {
        bytes32 value = IWordOracle(oracle).tagOf(account, flag);
        label = value;
        return value;
    }

    function route(address oracle, uint256 amount, uint8 raw) external returns (uint256) {
        IWordOracle.Mode mode = IWordOracle.Mode(raw);
        uint256 value = IWordOracle(oracle).quoteMode(amount, mode);
        saved = IWordOracle(oracle).quoteMode(amount, IWordOracle.Mode.Static);
        return value;
    }

    function either(address first, address second) external view returns (bool) {
        return pick(first, second);
    }

    function pick(address first, address second) internal view returns (bool) {
        bool ok = IWordOracle(first).allowed(second) || IWordOracle(second).allowed(first);
        return ok;
    }

    function stored() external view returns (uint256, bytes32) {
        return (saved, label);
    }
}
