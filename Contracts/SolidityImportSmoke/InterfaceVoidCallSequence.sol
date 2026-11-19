// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface INotified {
    function ping(uint256 amount) external;
    function relay(address caller, bytes calldata data) external;
    function poke() external;
    function fund(address to, uint128 amount, bool flag) external payable;
    enum Kind { First, Second }
    function notifyKind(address to, uint256 value, Kind kind) external;
    function notifyWord(address to, Kind kind) external returns (bytes32);
}

/// Typed external calls to functions without return values, as whole expression
/// statements: scalar, `enum`, calldata-bytes (`msg.data` and a parameter) and empty
/// argument lists, and a `payable` function called without value; and one `nonpayable`
/// call with a `bytes32` result and an `enum` argument. solc reverts with no data when
/// the target has no code, forwards a failed call's return data and ignores a successful
/// call's return data. State is written before each call, so every call is trailing.
contract InterfaceVoidCallFixture {
    uint256 private calls;
    uint256 private lastAmount;

    function ping(address target, uint256 amount) external {
        calls += 1;
        lastAmount = amount;
        INotified(target).ping(amount);
    }

    function relay(address target) external {
        calls += 1;
        INotified(target).relay(msg.sender, msg.data);
    }

    function relayData(address target, bytes calldata data) external {
        calls += 1;
        INotified(target).relay(msg.sender, data);
    }

    function poke(address target) external {
        INotified(target).poke();
    }

    function fund(address target, uint128 amount) external {
        lastAmount = amount;
        INotified(target).fund(target, amount, amount % 2 == 1);
    }

    function signal(address target, address to, uint8 raw) external {
        calls += 1;
        INotified.Kind kind = INotified.Kind(raw);
        INotified(target).notifyKind(to, lastAmount, kind);
    }

    /// A `nonpayable` function with a `bytes32` result: solc expects return data, so it
    /// skips the code check and reverts with no data on fewer than 32 return bytes.
    function signalWord(address target, address to, uint8 raw) external returns (bytes32) {
        calls += 1;
        INotified.Kind kind = INotified.Kind(raw);
        bytes32 word = INotified(target).notifyWord(to, kind);
        return word;
    }

    function read() external view returns (uint256, uint256) {
        return (calls, lastAmount);
    }
}
