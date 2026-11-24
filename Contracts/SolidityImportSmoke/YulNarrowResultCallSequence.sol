// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IYulNarrowResultToken {
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
    function approve(address spender, uint256 amount) external returns (bool);
}

/// Library helpers whose named `bool` result is written by an inline-assembly `call` and read
/// back in Yul: success only when the call succeeded and returned the word 1, or returned no
/// data from an account with code; a failed call's return data is bubbled when `bubble` is set.
/// Any other return word (`0`, `2`, a short or long answer) is a failure, so the exact raw word
/// decides which calls succeed.
library YulNarrowResultCallLib {
    function transferFlag(address token, address to, uint256 amount, bool bubble)
        internal returns (bool success)
    {
        bytes4 selector = IYulNarrowResultToken.transfer.selector;
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            mstore(0x00, selector)
            mstore(0x04, and(to, shr(96, not(0))))
            mstore(0x24, amount)
            success := call(gas(), token, 0, 0x00, 0x44, 0x00, 0x20)
            if iszero(and(success, eq(mload(0x00), 1))) {
                if and(iszero(success), bubble) {
                    returndatacopy(fmp, 0x00, returndatasize())
                    revert(fmp, returndatasize())
                }
                success := and(success, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
            }
            mstore(0x40, fmp)
        }
    }

    function transferFromFlag(address token, address from, address to, uint256 amount, bool bubble)
        internal returns (bool success)
    {
        bytes4 selector = IYulNarrowResultToken.transferFrom.selector;
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            mstore(0x00, selector)
            mstore(0x04, and(from, shr(96, not(0))))
            mstore(0x24, and(to, shr(96, not(0))))
            mstore(0x44, amount)
            success := call(gas(), token, 0, 0x00, 0x64, 0x00, 0x20)
            if iszero(and(success, eq(mload(0x00), 1))) {
                if and(iszero(success), bubble) {
                    returndatacopy(fmp, 0x00, returndatasize())
                    revert(fmp, returndatasize())
                }
                success := and(success, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
            }
            mstore(0x40, fmp)
            mstore(0x60, 0)
        }
    }

    function approveFlag(address token, address spender, uint256 amount, bool bubble)
        internal returns (bool success)
    {
        bytes4 selector = IYulNarrowResultToken.approve.selector;
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            mstore(0x00, selector)
            mstore(0x04, and(spender, shr(96, not(0))))
            mstore(0x24, amount)
            success := call(gas(), token, 0, 0x00, 0x44, 0x00, 0x20)
            if iszero(and(success, eq(mload(0x00), 1))) {
                if and(iszero(success), bubble) {
                    returndatacopy(fmp, 0x00, returndatasize())
                    revert(fmp, returndatasize())
                }
                success := and(success, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
            }
            mstore(0x40, fmp)
        }
    }

    /// The `bool` result is written from a Yul expression and read through a `bool` parameter.
    function tryMul(uint256 a, uint256 b) internal pure returns (bool success, uint256 result) {
        unchecked {
            uint256 c = a * b;
            assembly ("memory-safe") {
                success := or(eq(div(c, a), b), iszero(a))
            }
            result = c * toUint(success);
        }
    }

    function toUint(bool b) internal pure returns (uint256 u) {
        assembly ("memory-safe") {
            u := iszero(iszero(b))
        }
    }

    function saturatingMul(uint256 a, uint256 b) internal pure returns (uint256) {
        (bool success, uint256 result) = tryMul(a, b);
        return ternary(success, result, type(uint256).max);
    }

    /// `condition ? a : b` without a branch; the `bool` reaches Yul through a parameter.
    function ternary(bool condition, uint256 a, uint256 b) internal pure returns (uint256) {
        unchecked {
            return b ^ ((a ^ b) * toUint(condition));
        }
    }
}

/// State is written before each call, so every call is the function's last interaction.
contract YulNarrowResultCallFixture {
    uint256 private pushes;
    uint256 private lastAmount;

    error CallFailed(address target);

    function push(address token, address to, uint256 amount) external {
        pushes += 1;
        lastAmount = amount;
        if (!YulNarrowResultCallLib.transferFlag(token, to, amount, true)) revert CallFailed(token);
    }

    function tryPush(address token, address to, uint256 amount) external returns (bool) {
        pushes += 1;
        return YulNarrowResultCallLib.transferFlag(token, to, amount, false);
    }

    function pull(address token, address from, address to, uint256 amount) external {
        pushes += 1;
        if (!YulNarrowResultCallLib.transferFromFlag(token, from, to, amount, true)) revert CallFailed(token);
    }

    function allow(address token, address spender, uint256 amount) external returns (uint256 raw) {
        lastAmount = amount;
        bool ok = YulNarrowResultCallLib.approveFlag(token, spender, amount, false);
        assembly ("memory-safe") {
            raw := ok
        }
    }

    function scaled(uint256 a, uint256 b) external pure returns (uint256) {
        return YulNarrowResultCallLib.saturatingMul(a, b);
    }

    function read() external view returns (uint256, uint256) {
        return (pushes, lastAmount);
    }
}
