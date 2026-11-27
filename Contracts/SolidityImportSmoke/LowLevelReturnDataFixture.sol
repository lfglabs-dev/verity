// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Clean-room OpenZeppelin v5 `Errors` / `LowLevelCall` / `Address` fixture for R7.
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

/// Every storage access precedes the external CALL (checks-effects-interactions):
/// only local computation, memory writes, returns and reverts follow it.
contract LowLevelReturnDataFixture {
    uint256 private calls;

    function callRawBytes(address target, bytes calldata payload) external returns (bytes memory) {
        calls += 1;
        return Address.functionCall(target, payload);
    }

    function callDecodeWord(address target, bytes calldata payload) external returns (uint256) {
        calls += 1;
        return abi.decode(Address.functionCall(target, payload), (uint256));
    }

    function callWithValueDecode(address target, bytes calldata payload, uint256 value)
        external
        returns (uint256)
    {
        calls += 1;
        bytes memory ret = Address.functionCallWithValue(target, payload, value);
        return abi.decode(ret, (uint256));
    }

    function callDiscard(address target, bytes calldata payload) external returns (uint256) {
        uint256 count = calls + 1;
        calls = count;
        Address.functionCall(target, payload);
        return count;
    }

    function staticCallRawBytes(address target, bytes calldata payload) external view returns (bytes memory) {
        return Address.functionStaticCall(target, payload);
    }

    function staticCallDecodeWord(address target, bytes calldata payload) external view returns (uint256) {
        return abi.decode(Address.functionStaticCall(target, payload), (uint256));
    }

    function directReturnData(address target, bytes calldata payload) external returns (bool, uint256) {
        calls += 1;
        bool ok = LowLevelCall.callNoReturn(target, 0, payload);
        bytes memory rd = LowLevelCall.returnData();
        return (ok, rd.length);
    }

    function directReturnDataLength(address target, bytes calldata payload) external view returns (bool, uint256) {
        bool ok = LowLevelCall.staticcallNoReturn(target, payload);
        return (ok, LowLevelCall.returnData().length);
    }

    function readState() external view returns (uint256) {
        return calls;
    }
}

/// Negative control: delegatecall via Address must stay rejected.
library DelegateCallLib {
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        (bool ok, bytes memory ret) = target.delegatecall(data);
        require(ok);
        return ret;
    }
}

contract LowLevelDelegateCallRejected {
    function exec(address target, bytes calldata payload) external returns (bytes memory) {
        return DelegateCallLib.functionDelegateCall(target, payload);
    }
}
