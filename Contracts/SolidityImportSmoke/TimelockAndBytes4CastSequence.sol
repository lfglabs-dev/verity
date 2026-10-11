// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    bytes4 private constant ERC4906_INTERFACE_ID = bytes4(0x49064906);
    bytes4 private constant ERC165_INTERFACE_ID = bytes4(0x01ffc9a7);
    bytes4 private constant ZERO_INTERFACE_ID = bytes4(0);
    uint256 internal constant _DONE_TIMESTAMP = uint256(1);

    enum OperationState {
        Unset,
        Waiting,
        Ready,
        Done
    }

    error TimelockInsufficientDelay(uint256 delay, uint256 minDelay);
    error TimelockUnexpectedOperationState(bytes32 operationId, bytes32 expectedStates);
    error TimelockUnexecutedPredecessor(bytes32 predecessorId);
    error TimelockUnauthorizedCaller(address caller, address selfAddr, uint256 selfBal);

    event CallSalt(bytes32 indexed id, bytes32 salt);
    event Cancelled(bytes32 indexed id);
    event MinDelayChange(uint256 oldDuration, uint256 newDuration);

    mapping(bytes32 id => uint256) private _timestamps;
    uint256 private _minDelay;
    uint256 private totalScore;
    bytes32 private lastOperationId;

    function supportsInterface(bytes4 interfaceId) public pure returns (bool) {
        return
            interfaceId != ZERO_INTERFACE_ID &&
            (interfaceId == ERC4906_INTERFACE_ID || interfaceId == ERC165_INTERFACE_ID);
    }

    function _encodeStateBitmap(OperationState operationState) internal pure returns (bytes32) {
        return bytes32(1 << uint8(operationState));
    }

    function getTimestamp(bytes32 id) public view returns (uint256) {
        return _timestamps[id];
    }

    function getOperationState(bytes32 id) public view returns (OperationState) {
        uint256 timestamp = getTimestamp(id);
        if (timestamp == 0) {
            return OperationState.Unset;
        } else if (timestamp == _DONE_TIMESTAMP) {
            return OperationState.Done;
        } else if (timestamp > block.timestamp) {
            return OperationState.Waiting;
        } else {
            return OperationState.Ready;
        }
    }

    function isOperation(bytes32 id) public view returns (bool) {
        return getOperationState(id) != OperationState.Unset;
    }

    function isOperationPending(bytes32 id) public view returns (bool) {
        OperationState state = getOperationState(id);
        return state == OperationState.Waiting || state == OperationState.Ready;
    }

    function isOperationReady(bytes32 id) public view returns (bool) {
        return getOperationState(id) == OperationState.Ready;
    }

    function isOperationDone(bytes32 id) public view returns (bool) {
        return getOperationState(id) == OperationState.Done;
    }

    function getMinDelay() public view returns (uint256) {
        return _minDelay;
    }

    function hashOperation(
        address target,
        uint256 value,
        bytes calldata data,
        bytes32 predecessor,
        bytes32 salt
    ) public pure returns (bytes32) {
        return keccak256(abi.encode(target, value, data, predecessor, salt));
    }

    function _hashOperationMemory(
        address target,
        uint256 value,
        bytes memory data,
        string memory label,
        bytes32 predecessor,
        bytes32 salt
    ) internal pure returns (bytes32) {
        return keccak256(abi.encode(target, value, data, label, predecessor, salt));
    }

    function _schedule(bytes32 id, uint256 delay) private {
        if (isOperation(id)) {
            revert TimelockUnexpectedOperationState(id, _encodeStateBitmap(OperationState.Unset));
        }
        uint256 minDelay = getMinDelay();
        if (delay < minDelay) {
            revert TimelockInsufficientDelay(delay, minDelay);
        }
        _timestamps[id] = block.timestamp + delay;
    }

    function _cancel(bytes32 id) private {
        if (!isOperationPending(id)) {
            revert TimelockUnexpectedOperationState(
                id,
                _encodeStateBitmap(OperationState.Waiting) | _encodeStateBitmap(OperationState.Ready)
            );
        }
        delete _timestamps[id];
        emit Cancelled(id);
    }

    function _beforeCall(bytes32 id, bytes32 predecessor) private view {
        if (!isOperationReady(id)) {
            revert TimelockUnexpectedOperationState(id, _encodeStateBitmap(OperationState.Ready));
        }
        if (predecessor != bytes32(0) && !isOperationDone(predecessor)) {
            revert TimelockUnexecutedPredecessor(predecessor);
        }
    }

    function _afterCall(bytes32 id) private {
        if (!isOperationReady(id)) {
            revert TimelockUnexpectedOperationState(id, _encodeStateBitmap(OperationState.Ready));
        }
        _timestamps[id] = _DONE_TIMESTAMP;
    }

    function change(uint256 input) external returns (uint256) {
        if (_minDelay == 0) {
            emit MinDelayChange(0, 10);
            _minDelay = 10;
        }

        bytes32 salt = bytes32((input & 0xff) + 1);
        bytes memory payload = bytes.concat(ERC4906_INTERFACE_ID, salt);
        uint256 opValue = (input & 0x3f) + 100;
        bytes32 opId = _hashOperationMemory(
            address(this),
            opValue,
            payload,
            "timelock-op",
            bytes32(0),
            salt
        );

        if (input == 21) {
            _cancel(opId);
        }
        if (input == 22) {
            revert TimelockUnauthorizedCaller(msg.sender, address(this), address(this).balance);
        }

        if (!isOperation(opId)) {
            uint256 delay = (input & 1) == 0 ? 0 : _minDelay + (input & 0x7);
            if (delay == 0) {
                _timestamps[opId] = block.timestamp;
            } else {
                _schedule(opId, delay);
            }
            emit CallSalt(opId, salt);
        }

        uint256 stateBonus;
        if (isOperationReady(opId)) {
            _beforeCall(opId, bytes32(0));
            _afterCall(opId);
            stateBonus = uint256(_encodeStateBitmap(OperationState.Done));
        } else if (isOperationPending(opId)) {
            _cancel(opId);
            stateBonus = uint256(_encodeStateBitmap(OperationState.Waiting));
        } else {
            stateBonus = uint256(_encodeStateBitmap(getOperationState(opId)));
        }

        bool is4906 = supportsInterface(ERC4906_INTERFACE_ID);
        bool isZero = supportsInterface(ZERO_INTERFACE_ID);
        uint256 interfaceTag = (is4906 && !isZero) ? uint256(uint32(ERC4906_INTERFACE_ID)) : 0;

        uint256 summary;
        unchecked {
            summary =
                (uint256(opId) & 0xffffffff) +
                interfaceTag +
                stateBonus +
                _timestamps[opId] +
                _minDelay;
        }

        totalScore += summary;
        lastOperationId = opId;
        require(input != 20, "TBC: rollback");
        return totalScore;
    }

    function fail() external {
        _minDelay = 999;
        totalScore += 777;
        revert("TBC: fail");
    }

    function read() external view returns (uint256, bytes32, uint256, uint256) {
        return (totalScore, lastOperationId, _minDelay, _timestamps[lastOperationId]);
    }
}
