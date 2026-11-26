// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface ISyntheticCallee {
    function ping(uint256 amount) external;
}

interface ISyntheticToken {
    function transfer(address to, uint256 amount) external returns (bool);
}

interface ISyntheticViewOracle {
    function peek() external view returns (uint256);
}

/// Storage reads and writes after a typed external call to a function without return
/// values. The callee may re-enter, so each post-call read observes whatever the call
/// left in this contract's storage.
contract SyntheticPostCallWrite {
    uint256 private counter;
    uint256 private total;

    error CounterMismatch(uint256 observed);

    function pingThenCount(address target, uint256 amount) external {
        ISyntheticCallee(target).ping(amount);
        counter = counter + 1;
        total += amount;
    }

    /// A storage read after the call, with no write.
    function pingThenRead(address target) external returns (uint256) {
        ISyntheticCallee(target).ping(0);
        return counter;
    }

    /// Two sequential closed calls with storage updates between and after them.
    function twoPingsThenCount(address first, address second, uint256 amount) external {
        ISyntheticCallee(first).ping(amount);
        counter += 1;
        ISyntheticCallee(second).ping(amount);
        total += amount;
    }

    /// A post-call `require` reading storage.
    function pingThenRequire(address target, uint256 expected) external {
        ISyntheticCallee(target).ping(0);
        uint256 observed = counter;
        require(observed == expected, CounterMismatch(observed));
        total += 1;
    }

    /// A closed call and storage write inside a bounded `for` loop.
    function pingLoop(address target, uint256 amount) external {
        for (uint256 i = 0; i < 2; i++) {
            ISyntheticCallee(target).ping(amount);
            counter += 1;
        }
        total += amount;
    }

    /// Reading `address(this).balance` after a closed call (`Expr.selfBalance`).
    function pingThenBalance(address target) external returns (uint256) {
        ISyntheticCallee(target).ping(0);
        return counter + address(this).balance;
    }

    /// A typed `view` call (`STATICCALL`) after a closed `CALL`.
    function pingThenView(address target, address oracle) external returns (uint256) {
        ISyntheticCallee(target).ping(0);
        return counter + ISyntheticViewOracle(oracle).peek();
    }

    function read() external view returns (uint256, uint256) {
        return (counter, total);
    }
}

/// Effects after an interaction: a value-free low-level `CALL` with optional-bool return
/// data, then a checked subtraction from and an addition to storage. A callee that
/// re-enters and spends the same credit makes the post-call subtraction panic, as on the EVM.
contract SyntheticCallbackTransfer {
    mapping(address => uint256) private credit;
    uint256 private transfers;

    function deposit(address account, uint256 amount) external {
        credit[account] += amount;
    }

    function transferOut(address token, address to, uint256 amount) external {
        require(credit[to] >= amount, "insufficient credit");
        (bool success, bytes memory returndata) =
            token.call(abi.encodeCall(ISyntheticToken.transfer, (to, amount)));
        if (!success) {
            assembly ("memory-safe") {
                revert(add(returndata, 0x20), mload(returndata))
            }
        }
        require(returndata.length == 0 || abi.decode(returndata, (bool)), "transfer returned false");
        credit[to] -= amount;
        transfers += 1;
    }

    function read(address account) external view returns (uint256, uint256) {
        return (credit[account], transfers);
    }
}

/// Logs after a typed external call, and storage reads/writes in the clauses of `try`.
contract SyntheticPostCallEvent {
    uint256 private count;
    uint256 private failures;

    event Notified(address indexed target, uint256 amount, uint256 count);

    function notify(address target, uint256 amount) external {
        ISyntheticCallee(target).ping(amount);
        count += 1;
        emit Notified(target, amount, count);
    }

    function tryNotify(address target, uint256 amount) external returns (uint256) {
        try ISyntheticCallee(target).ping(amount) {
            count += 1;
        } catch {
            failures += 1;
        }
        return count;
    }

    /// Reading storage in both `try` and `catch` clauses after a closed call.
    function tryNotifyRead(address target, uint256 amount) external returns (uint256) {
        try ISyntheticCallee(target).ping(amount) {
            return count;
        } catch {
            return failures;
        }
    }

    function read() external view returns (uint256, uint256) {
        return (count, failures);
    }
}
