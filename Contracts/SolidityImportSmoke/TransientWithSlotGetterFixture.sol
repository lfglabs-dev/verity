// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Clean-room OpenZeppelin v5 `Errors` / `LowLevelCall` / `Address` libraries for R9 + R9b.
library Errors {
    error InsufficientBalance(uint256 balance, uint256 needed);
    error FailedCall();
}

library LowLevelCall {
    function callNoReturn(address target, uint256 value, bytes memory data) internal returns (bool success) {
        assembly ("memory-safe") {
            success := call(gas(), target, value, add(data, 0x20), mload(data), 0x00, 0x00)
        }
    }

    function staticcallNoReturn(address target, bytes memory data) internal view returns (bool success) {
        assembly ("memory-safe") {
            success := staticcall(gas(), target, add(data, 0x20), mload(data), 0x00, 0x00)
        }
    }

    function returnDataSize() internal pure returns (uint256 size) {
        assembly ("memory-safe") {
            size := returndatasize()
        }
    }

    function returnData() internal pure returns (bytes memory result) {
        assembly ("memory-safe") {
            result := mload(0x40)
            mstore(result, returndatasize())
            returndatacopy(add(result, 0x20), 0x00, returndatasize())
            mstore(0x40, add(result, add(0x20, returndatasize())))
        }
    }

    function bubbleRevert() internal pure {
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            returndatacopy(fmp, 0x00, returndatasize())
            revert(fmp, returndatasize())
        }
    }
}

library Address {
    error AddressEmptyCode(address target);

    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0);
    }

    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        if (address(this).balance < value) {
            revert Errors.InsufficientBalance(address(this).balance, value);
        }
        bool success = LowLevelCall.callNoReturn(target, value, data);
        if (success && (LowLevelCall.returnDataSize() > 0 || target.code.length > 0)) {
            return LowLevelCall.returnData();
        } else if (success) {
            revert AddressEmptyCode(target);
        } else if (LowLevelCall.returnDataSize() > 0) {
            LowLevelCall.bubbleRevert();
        } else {
            revert Errors.FailedCall();
        }
    }

    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        bool success = LowLevelCall.staticcallNoReturn(target, data);
        if (success && (LowLevelCall.returnDataSize() > 0 || target.code.length > 0)) {
            return LowLevelCall.returnData();
        } else if (success) {
            revert AddressEmptyCode(target);
        } else if (LowLevelCall.returnDataSize() > 0) {
            LowLevelCall.bubbleRevert();
        } else {
            revert Errors.FailedCall();
        }
    }
}

/// Renamed library with identical Yul AST shapes (plus 1-arg bytes bubbleRevert) to prove
/// R9b admission is 100% AST-structural and library-name independent.
library CustomBridge {
    error EmptyTarget(address target);
    error CallFailed();

    function probeStatic(address dst, bytes memory payload) internal view returns (bool ok) {
        assembly ("memory-safe") {
            ok := staticcall(gas(), dst, add(0x20, payload), mload(payload), 0, 0)
        }
    }

    function rdLen() internal pure returns (uint256 n) {
        assembly ("memory-safe") {
            n := returndatasize()
        }
    }

    function rdCopy() internal pure returns (bytes memory out) {
        assembly ("memory-safe") {
            let sz := returndatasize()
            out := mload(0x40)
            mstore(out, sz)
            returndatacopy(add(out, 0x20), 0, sz)
            mstore(0x40, add(out, and(add(sz, 0x3f), not(0x1f))))
        }
    }

    function rethrowBytes(bytes memory errData) internal pure {
        assembly ("memory-safe") {
            revert(add(errData, 0x20), mload(errData))
        }
    }

    function execStatic(address dst, bytes memory payload) internal view returns (bytes memory) {
        bool ok = probeStatic(dst, payload);
        if (ok && (rdLen() > 0 || dst.code.length > 0)) {
            return rdCopy();
        } else if (ok) {
            revert EmptyTarget(dst);
        } else if (rdLen() > 0) {
            rethrowBytes(rdCopy());
        } else {
            revert CallFailed();
        }
    }
}

/// Clean-room fixture for R9 + R9b:
/// - R9: EIP-7201 constant-slot storage-pointer getters (`$.slot := STORE_SLOT` and literal)
///   combined with a `transient bool` state variable.
/// - R9b: Recognized structured OpenZeppelin v5 `LowLevelCall` helpers (`staticcallNoReturn`,
///   `callNoReturn`, `returnDataSize`, `returnData`, `bubbleRevert`) inside closures that also
///   read/write a `transient bool` state variable and use `$.slot := CONST`.
/// - Negative controls: arbitrary inline assembly, dynamic-slot assembly, non-structured Yul
///   call assembly, and both Solidity-level and Yul-level `delegatecall` remain REJECTED.
contract TransientWithSlotGetterFixture {
    struct Store {
        uint256 value;
        uint256 batchRuns;
        mapping(address => uint256) credits;
    }

    bytes32 private constant STORE_SLOT =
        0x1111111111111111111111111111111111111111111111111111111111111100;

    bool private transient _inBatch;

    function _getStore() private pure returns (Store storage $) {
        assembly {
            $.slot := STORE_SLOT
        }
    }

    function _getStoreLiteral() private pure returns (Store storage $) {
        assembly ("memory-safe") {
            $.slot := 0x1111111111111111111111111111111111111111111111111111111111111100
        }
    }

    function _getStoreDynamic(bytes32 slot) private pure returns (Store storage $) {
        assembly {
            $.slot := slot
        }
    }

    function _getStoreWithExtraAsm() private view returns (Store storage $) {
        assembly {
            $.slot := STORE_SLOT
        }
        uint256 junk;
        assembly {
            junk := tload(0)
        }
        if (junk == type(uint256).max) {
            revert();
        }
    }

    function _addValue(uint256 delta, address account) internal returns (uint256) {
        Store storage $ = _getStore();
        if (!_inBatch) {
            $.value += delta;
        } else {
            $.value += delta * 2;
            $.batchRuns += 1;
        }
        $.credits[account] += delta;
        return $.value;
    }

    function addDirect(uint256 delta, address account) external returns (uint256) {
        return _addValue(delta, account);
    }

    function addInBatch(uint256 a, uint256 b, address account) external returns (uint256) {
        require(!_inBatch, "reentrant batch");
        _inBatch = true;
        uint256 first = _addValue(a, account);
        Store storage $lit = _getStoreLiteral();
        $lit.value += b;
        uint256 total = $lit.value;
        _inBatch = false;
        return first + total;
    }

    function addInBatchRevert(uint256 delta, address account) external {
        _inBatch = true;
        _addValue(delta, account);
        require(false, "rollback");
    }

    function staticCallInBatch(address target, bytes calldata payload, address account)
        external
        returns (uint256)
    {
        require(!_inBatch, "reentrant batch");
        _inBatch = true;
        bytes memory ret = Address.functionStaticCall(target, payload);
        uint256 decoded = abi.decode(ret, (uint256));
        uint256 total = _addValue(decoded, account);
        _inBatch = false;
        return total;
    }

    function callInBatch(address target, bytes calldata payload, address account)
        external
        returns (uint256)
    {
        require(!_inBatch, "reentrant batch");
        _inBatch = true;
        bytes memory ret = Address.functionCall(target, payload);
        uint256 decoded = abi.decode(ret, (uint256));
        uint256 total = _addValue(decoded, account);
        _inBatch = false;
        return total;
    }

    function renamedStaticCallInBatch(address target, bytes calldata payload, address account)
        external
        returns (uint256)
    {
        require(!_inBatch, "reentrant batch");
        _inBatch = true;
        bytes memory ret = CustomBridge.execStatic(target, payload);
        uint256 decoded = abi.decode(ret, (uint256));
        uint256 total = _addValue(decoded, account);
        _inBatch = false;
        return total;
    }

    function readState(address account)
        external
        view
        returns (uint256 value, uint256 batchRuns, uint256 credit, bool inBatch)
    {
        Store storage $ = _getStore();
        return ($.value, $.batchRuns, $.credits[account], _inBatch);
    }

    // Negative control 1: arbitrary tload assembly in a transient closure
    function badArbitraryAsm() external returns (uint256 word) {
        _inBatch = true;
        Store storage $ = _getStore();
        $.value += 1;
        assembly {
            word := tload(0)
        }
    }

    // Negative control 2: dynamic/parameter slot binding in a transient closure
    function badDynamicSlotAsm(bytes32 slot) external returns (uint256) {
        _inBatch = true;
        Store storage $ = _getStoreDynamic(slot);
        $.value += 1;
        return $.value;
    }

    // Negative control 3: multi-statement assembly in a storage-pointer getter in a transient closure
    function badExtraAsmInGetter() external returns (uint256) {
        _inBatch = true;
        Store storage $ = _getStoreWithExtraAsm();
        $.value += 1;
        return $.value;
    }

    // Negative control 4: Solidity delegatecall in a transient closure
    function badDelegateCallInTransient(address target, bytes calldata payload)
        external
        returns (bytes memory)
    {
        _inBatch = true;
        (bool ok, bytes memory ret) = target.delegatecall(payload);
        require(ok);
        _inBatch = false;
        return ret;
    }

    // Negative control 5: Yul delegatecall in a transient closure
    function badYulDelegateCallInTransient(address target, bytes memory payload)
        external
        returns (bool ok)
    {
        _inBatch = true;
        assembly ("memory-safe") {
            ok := delegatecall(gas(), target, add(payload, 0x20), mload(payload), 0x00, 0x00)
        }
        _inBatch = false;
    }

    // Negative control 6: non-structured scratch-space Yul call in a transient closure
    function badNonStructuredCallAsmInTransient(address target) external returns (bool ok) {
        _inBatch = true;
        assembly {
            ok := call(gas(), target, 0, 0, 0, 0, 0)
        }
        _inBatch = false;
    }
}
