// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IReceiverHook {
    function onReceived(address from, uint256 id) external returns (bytes4);
    function quote(uint256 amount) external view returns (uint256);
    function flag() external returns (bool);
    function notify(uint256 amount) external;
}

/// External `try` statements of interface members with a return value, a `view` callee and
/// a `catch (bytes memory reason)` clause. A successful call of a function with a return
/// value decodes its first word before the success clause, reverting uncaught with no data
/// on short or out-of-range return data; a failed call runs the catch clause with the
/// complete revert data. State is written before each call, so every call is trailing.
contract TryCatchMock {
    error BadReceiver(address to);

    uint256 private calls;

    /// Acceptance-check shape: the returned selector is compared; a failure with data is
    /// forwarded, an empty failure becomes a custom error.
    function check(address to, uint256 id) external {
        calls += 1;
        try IReceiverHook(to).onReceived(msg.sender, id) returns (bytes4 retval) {
            if (retval != IReceiverHook.onReceived.selector) revert BadReceiver(to);
        } catch (bytes memory reason) {
            if (reason.length == 0) revert BadReceiver(to);
            assembly {
                revert(add(32, reason), mload(reason))
            }
        }
    }

    /// A `view` callee runs as a `staticcall`; the result is returned or replaced.
    function quoteOr(address oracle, uint256 amount, uint256 fallbackValue)
        external
        view
        returns (uint256)
    {
        try IReceiverHook(oracle).quote(amount) returns (uint256 v) {
            return v;
        } catch {
            return fallbackValue;
        }
    }

    /// The `bool` result is decoded and validated even when the clause does not name it.
    function poke(address to) external returns (uint256) {
        calls += 2;
        try IReceiverHook(to).flag() {
            return 1;
        } catch (bytes memory reason) {
            return 100 + reason.length;
        }
    }

    /// A function without return values with a revert-data catch clause.
    function notifyOr(address to, uint256 amount) external returns (uint256) {
        calls += 3;
        try IReceiverHook(to).notify(amount) {
            return 0;
        } catch (bytes memory reason) {
            return 1000 + reason.length;
        }
    }

    /// The acceptance check inside an inlined `void` helper.
    function checkViaHelper(address to, uint256 id) external {
        calls += 4;
        _check(to, id);
    }

    function _check(address to, uint256 id) private {
        try IReceiverHook(to).onReceived(address(this), id) returns (bytes4 retval) {
            if (retval != IReceiverHook.onReceived.selector) revert BadReceiver(to);
        } catch {
            revert BadReceiver(to);
        }
    }

    function read() external view returns (uint256) {
        return calls;
    }
}
