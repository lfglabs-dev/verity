// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Configurable test counterpart for imported external-call models.
contract TokenMock {
    enum Mode { Normal, FeeOnTransfer, ReturnsFalse, Reverts }
    Mode public mode;
    uint256 public feeBps;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    address public callback;
    bytes public callbackData;
    bool private callbackActive;

    error TransferRejected();
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    function configure(Mode mode_, uint256 feeBps_, address callback_, bytes calldata data) external {
        require(feeBps_ <= 10_000, "fee exceeds transfer");
        mode = mode_;
        feeBps = feeBps_;
        callback = callback_;
        callbackData = data;
    }

    function mint(address to, uint256 amount) external {
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        return move(msg.sender, to, amount);
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        if (mode == Mode.ReturnsFalse) return false;
        if (mode == Mode.Reverts) revert TransferRejected();
        uint256 permitted = allowance[from][msg.sender];
        if (permitted != type(uint256).max) allowance[from][msg.sender] = permitted - amount;
        return move(from, to, amount);
    }

    function move(address from, address to, uint256 amount) private returns (bool) {
        if (mode == Mode.ReturnsFalse) return false;
        if (mode == Mode.Reverts) revert TransferRejected();
        uint256 fee = mode == Mode.FeeOnTransfer ? amount * feeBps / 10_000 : 0;
        balanceOf[from] -= amount;
        balanceOf[to] += amount - fee;
        totalSupply -= fee;
        emit Transfer(from, to, amount - fee);
        if (fee != 0) emit Transfer(from, address(0), fee);
        if (callback != address(0) && !callbackActive) {
            callbackActive = true;
            (bool ok, bytes memory data) = callback.call(callbackData);
            if (!ok) assembly { revert(add(data, 32), mload(data)) }
            callbackActive = false;
        }
        return true;
    }
}

contract OracleMock {
    uint256 public answer;
    bool public reject;
    error OracleRejected();

    function configure(uint256 answer_, bool reject_) external {
        answer = answer_;
        reject = reject_;
    }

    function price() external view returns (uint256) {
        if (reject) revert OracleRejected();
        return answer;
    }
}

contract CallbackMock {
    address public target;
    bytes public data;
    bool public propagateFailure;
    uint256 public calls;
    bool public lastSuccess;
    bytes public lastResult;

    function configure(address target_, bytes calldata data_, bool propagateFailure_) external {
        target = target_;
        data = data_;
        propagateFailure = propagateFailure_;
    }

    function invoke() external {
        calls += 1;
        (bool ok, bytes memory result) = target.call(data);
        lastSuccess = ok;
        lastResult = result;
        if (!ok && propagateFailure) assembly { revert(add(result, 32), mload(result)) }
    }
}
