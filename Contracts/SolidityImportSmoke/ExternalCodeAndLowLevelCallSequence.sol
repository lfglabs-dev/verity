// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IToken {
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

library SafeCallLib {
    error NoCode();
    error TransferReturnedFalse();
    error TransferFromReturnedFalse();

    function safeTransfer(address token, address to, uint256 amount) internal {
        require(token.code.length > 0, NoCode());

        (bool success, bytes memory returndata) = token.call(abi.encodeCall(IToken.transfer, (to, amount)));
        if (!success) {
            assembly ("memory-safe") {
                revert(add(returndata, 0x20), mload(returndata))
            }
        }
        require(returndata.length == 0 || abi.decode(returndata, (bool)), TransferReturnedFalse());
    }

    function safeTransferFrom(address token, address from, address to, uint256 amount) internal {
        require(token.code.length > 0, NoCode());

        (bool success, bytes memory returndata) =
            token.call(abi.encodeCall(IToken.transferFrom, (from, to, amount)));
        if (!success) {
            assembly ("memory-safe") {
                revert(add(returndata, 0x20), mload(returndata))
            }
        }
        require(returndata.length == 0 || abi.decode(returndata, (bool)), TransferFromReturnedFalse());
    }
}

contract ExternalCodeAndLowLevelCallFixture {
    uint256 private reserve;
    uint256 private payments;
    mapping(address => uint256) private credit;

    event Paid(address indexed token, address indexed to, uint256 amount);

    function codeSize(address account) external view returns (uint256) {
        return account.code.length;
    }

    function hasCode(address account) external view returns (bool) {
        return account.code.length > 0;
    }

    function deposit(address token, uint256 amount) external {
        credit[msg.sender] += amount;
        reserve += amount;
        SafeCallLib.safeTransferFrom(token, msg.sender, address(this), amount);
    }

    function withdraw(address token, address to, uint256 amount) external {
        credit[msg.sender] -= amount;
        reserve -= amount;
        emit Paid(token, to, amount);
        SafeCallLib.safeTransfer(token, to, amount);
    }

    function pay(address token, address to, uint256 amount) external {
        payments += 1;
        (bool success, bytes memory returndata) = token.call(abi.encodeCall(IToken.transfer, (to, amount)));
        if (!success) {
            assembly ("memory-safe") {
                revert(add(returndata, 0x20), mload(returndata))
            }
        }
        require(returndata.length == 0 || abi.decode(returndata, (bool)), "transfer returned false");
    }

    function stored(address account) external view returns (uint256, uint256, uint256) {
        return (reserve, payments, credit[account]);
    }
}
