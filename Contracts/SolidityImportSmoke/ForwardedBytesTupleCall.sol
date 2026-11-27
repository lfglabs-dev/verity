// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

enum Operation {
    Call,
    DelegateCall
}

interface IAvatar {
    function execTransactionFromModuleReturnData(
        address to,
        uint256 value,
        bytes memory data,
        Operation operation
    ) external returns (bool success, bytes memory returnData);
}

interface IEnumAvatar {
    function execEnum(uint256 x) external returns (Operation op, bytes memory returnData);
}

/// Smoke fixture mirroring Zodiac Roles v3 `execTransactionFromModuleReturnData` ->
/// `_execWithRoleReturnData` (`Roles.sol:202:9`): typed external interface `CALL`
/// returning `(Scalar, bytes memory)` assigned inside a forwarded `(Scalar, bytes memory)`
/// tuple helper, with post-call `revert`, post-call storage writes, and a `nonReentrant`
/// modifier epilogue.
contract ForwardedBytesTupleCall {
    error ModuleTransactionFailed();
    error Reentrancy();

    uint256 private _locked;
    uint256 public persistCount;
    uint256 public cbCount;
    address public target;

    modifier nonReentrant() {
        if (_locked != 0) revert Reentrancy();
        _locked = 1;
        _;
        _locked = 0;
    }

    function setTarget(address t) external {
        target = t;
    }

    function pingCallback() external {
        cbCount += 1;
    }

    function guardedPing() external nonReentrant {
        cbCount += 1;
    }

    function state() external view returns (uint256, uint256, uint256) {
        return (persistCount, cbCount, _locked);
    }

    function _exec(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bool shouldRevert
    ) private returns (bool success, bytes memory returnData) {
        (success, returnData) = IAvatar(target).execTransactionFromModuleReturnData(
            to,
            value,
            data,
            operation
        );
        if (shouldRevert && !success) {
            revert ModuleTransactionFailed();
        }
        if (success) {
            persistCount += 1;
        }
    }

    function exec(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bool shouldRevert
    ) external nonReentrant returns (bool success, bytes memory returnData) {
        return _exec(to, value, data, operation, shouldRevert);
    }

    function execUnlocked(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bool shouldRevert
    ) external returns (bool success, bytes memory returnData) {
        return _exec(to, value, data, operation, shouldRevert);
    }

    function _execEnum(uint256 x) private returns (Operation op, bytes memory returnData) {
        (op, returnData) = IEnumAvatar(target).execEnum(x);
        persistCount += 1;
    }

    function execEnum(uint256 x) external returns (Operation op, bytes memory returnData) {
        return _execEnum(x);
    }
}
