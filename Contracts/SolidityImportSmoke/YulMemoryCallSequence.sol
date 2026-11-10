// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface ITokenCalls {
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

interface IAuthorityQuery {
    function canCall(address caller, address target, bytes4 selector) external view returns (bool, uint32);
}

/// Inline-assembly external calls over memory: a value-free `call` whose calldata is written to
/// the scratch space (overwriting the free-memory pointer and, for four words, the zero slot,
/// both restored), with a bubbled revert and an empty-returndata code check; and a `staticcall`
/// whose calldata is an `abi.encodeCall` buffer and whose two return words land in the scratch
/// space. State is written before each call, so every call is a trailing interaction.
contract YulMemoryCallFixture {
    uint256 private pushes;
    uint256 private pulls;
    uint256 private lastAmount;

    error CallFailed(address target);

    function push(address token, address to, uint256 amount) external returns (bool ok) {
        pushes += 1;
        lastAmount = amount;
        bytes4 selector = ITokenCalls.transfer.selector;
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            mstore(0x00, selector)
            mstore(0x04, and(to, shr(96, not(0))))
            mstore(0x24, amount)
            ok := call(gas(), token, 0, 0x00, 0x44, 0x00, 0x20)
            if iszero(and(ok, eq(mload(0x00), 1))) {
                if iszero(ok) {
                    returndatacopy(fmp, 0x00, returndatasize())
                    revert(fmp, returndatasize())
                }
                ok := and(ok, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
            }
            mstore(0x40, fmp)
        }
        require(ok, CallFailed(token));
    }

    function pull(address token, address from, address to, uint256 amount) external returns (bool ok) {
        pulls += 1;
        bytes4 selector = ITokenCalls.transferFrom.selector;
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            mstore(0x00, selector)
            mstore(0x04, and(from, shr(96, not(0))))
            mstore(0x24, and(to, shr(96, not(0))))
            mstore(0x44, amount)
            ok := call(gas(), token, 0, 0x00, 0x64, 0x00, 0x20)
            if iszero(and(ok, eq(mload(0x00), 1))) {
                if iszero(ok) {
                    returndatacopy(fmp, 0x00, returndatasize())
                    revert(fmp, returndatasize())
                }
                ok := and(ok, and(iszero(returndatasize()), gt(extcodesize(token), 0)))
            }
            mstore(0x40, fmp)
            mstore(0x60, 0)
        }
    }

    function query(address authority, address caller, address target, bytes4 selector)
        external
        view
        returns (bool immediate, uint32 delay)
    {
        bytes memory data = abi.encodeCall(IAuthorityQuery.canCall, (caller, target, selector));
        assembly ("memory-safe") {
            mstore(0x00, 0x00)
            mstore(0x20, 0x00)
            if staticcall(gas(), authority, add(data, 0x20), mload(data), 0x00, 0x40) {
                immediate := mload(0x00)
                delay := mload(0x20)
                delay := mul(delay, iszero(shr(32, delay)))
            }
        }
    }

    function codeSize(address account) external view returns (uint256 size) {
        assembly ("memory-safe") {
            size := extcodesize(account)
        }
    }

    function read() external view returns (uint256, uint256, uint256) {
        return (pushes, pulls, lastAmount);
    }
}
