// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Low-level `target.call{value: v}(data)` declarations. solc sends `data` as the complete
/// calldata with `v` wei; an underfunded call fails without reaching the target; a failed
/// call refunds the value; `success` and the complete return data are bound as locals and
/// nothing reverts by itself. State is written before each call, so every call is trailing.
contract EthSender {
    error FailedCall();

    uint256 private sent;

    /// The success bit decides a custom error; return data is not bound.
    function execute(address target, uint256 value, bytes calldata data) external {
        sent += value;
        (bool success, ) = target.call{value: value}(data);
        if (!success) revert FailedCall();
    }

    /// Plain value transfer to a `payable(...)` conversion, with empty calldata and a `require`.
    function sendValue(address recipient, uint256 amount) external {
        sent += amount;
        (bool ok, ) = payable(recipient).call{value: amount}("");
        require(ok, "send failed");
    }

    /// The complete return data is forwarded on failure and measured on success.
    function forward(address target, uint256 value, bytes memory data)
        external
        returns (uint256)
    {
        sent += 1;
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        if (!success) {
            assembly {
                revert(add(returndata, 0x20), mload(returndata))
            }
        }
        return returndata.length;
    }

    /// Both results are returned: a failure is observable, not a revert.
    function probe(address target, uint256 value) external returns (bool, uint256) {
        sent += 2;
        (bool success, bytes memory returndata) =
            target.call{value: value}(abi.encodeWithSignature("ping(uint256)", value));
        return (success, returndata.length);
    }

    /// The same transfer inside an inlined `void` helper.
    function sendViaHelper(address to, uint256 amount) external {
        sent += 3;
        _send(payable(to), amount);
    }

    function _send(address payable to, uint256 amount) private {
        (bool ok, ) = to.call{value: amount}("");
        if (!ok) revert FailedCall();
    }

    function read() external view returns (uint256) {
        return sent;
    }

    function contractBalance() external view returns (uint256) {
        return address(this).balance;
    }
}
