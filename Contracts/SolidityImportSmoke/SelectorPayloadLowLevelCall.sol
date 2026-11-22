// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;
// A private helper that performs the CALL with the payload, rejects a target without code when
// nothing is returned, bubbles a failure, and requires an optional `true` (the structure of
// OpenZeppelin 4.x `SafeERC20._callOptionalReturn` through `Address.functionCall`). It is lowered
// through its body like any other helper.

interface ITarget {
    function ping(address to, uint256 amount) external returns (bool);
}

contract SelectorPayloadLowLevelCall {
    uint256 private first = 7;
    uint256 private second = 9;

    function _callOptionalReturn(address token, bytes memory data) private {
        (bool success, bytes memory returndata) = token.call(data);
        if (success) {
            if (returndata.length == 0) require(token.code.length > 0, "call to non-contract");
        } else {
            revert("low-level call failed");
        }
        require(returndata.length == 0 || abi.decode(returndata, (bool)), "operation did not succeed");
    }

    function send(address token, uint256 amount) external {
        _callOptionalReturn(token, abi.encodeWithSelector(ITarget.ping.selector, msg.sender, amount));
    }
}
