// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library Create2Slice41 {
    function computeAddress(bytes32 salt, bytes32 bytecodeHash) internal view returns (address) {
        return computeAddress(salt, bytecodeHash, address(this));
    }

    function computeAddress(bytes32 salt, bytes32 bytecodeHash, address deployer) internal pure returns (address addr) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(ptr, 0x40), bytecodeHash)
            mstore(add(ptr, 0x20), salt)
            mstore(ptr, deployer)
            let start := add(ptr, 0x0b)
            mstore8(start, 0xff)
            addr := keccak256(start, 85)
        }
    }
}

library ClonesSlice41 {
    function predictDeterministicAddress(
        address implementation,
        bytes32 salt,
        address deployer
    ) internal pure returns (address predicted) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(add(ptr, 0x38), deployer)
            mstore(add(ptr, 0x24), 0x5af43d82803e903d91602b57fd5bf3ff)
            mstore(add(ptr, 0x14), implementation)
            mstore(ptr, 0x3d602d80600a3d3981f3363d3d373d3d3d363d73)
            mstore(add(ptr, 0x58), salt)
            mstore(add(ptr, 0x78), keccak256(add(ptr, 0x0c), 0x37))
            predicted := keccak256(add(ptr, 0x43), 0x55)
        }
    }

    function predictDeterministicAddress(
        address implementation,
        bytes32 salt
    ) internal view returns (address predicted) {
        return predictDeterministicAddress(implementation, salt, address(this));
    }
}

library DoubleEndedQueueSlice41 {
    error QueueFull();
    error QueueEmpty();
    error QueueOutOfBounds();

    struct Bytes32Deque {
        uint128 _begin;
        uint128 _end;
        mapping(uint128 index => bytes32) _data;
    }

    function pushBack(Bytes32Deque storage deque, bytes32 value) internal {
        unchecked {
            uint128 backIndex = deque._end;
            if (backIndex + 1 == deque._begin) revert QueueFull();
            deque._data[backIndex] = value;
            deque._end = backIndex + 1;
        }
    }

    function popBack(Bytes32Deque storage deque) internal returns (bytes32 value) {
        unchecked {
            uint128 backIndex = deque._end;
            if (backIndex == deque._begin) revert QueueEmpty();
            --backIndex;
            value = deque._data[backIndex];
            delete deque._data[backIndex];
            deque._end = backIndex;
        }
    }

    function pushFront(Bytes32Deque storage deque, bytes32 value) internal {
        unchecked {
            uint128 frontIndex = deque._begin - 1;
            if (frontIndex == deque._end) revert QueueFull();
            deque._data[frontIndex] = value;
            deque._begin = frontIndex;
        }
    }

    function popFront(Bytes32Deque storage deque) internal returns (bytes32 value) {
        unchecked {
            uint128 frontIndex = deque._begin;
            if (frontIndex == deque._end) revert QueueEmpty();
            value = deque._data[frontIndex];
            delete deque._data[frontIndex];
            deque._begin = frontIndex + 1;
        }
    }

    function front(Bytes32Deque storage deque) internal view returns (bytes32 value) {
        if (empty(deque)) revert QueueEmpty();
        return deque._data[deque._begin];
    }

    function back(Bytes32Deque storage deque) internal view returns (bytes32 value) {
        if (empty(deque)) revert QueueEmpty();
        unchecked {
            return deque._data[deque._end - 1];
        }
    }

    function at(Bytes32Deque storage deque, uint256 index) internal view returns (bytes32 value) {
        if (index >= length(deque)) revert QueueOutOfBounds();
        unchecked {
            return deque._data[deque._begin + uint128(index)];
        }
    }

    function clear(Bytes32Deque storage deque) internal {
        deque._begin = 0;
        deque._end = 0;
    }

    function length(Bytes32Deque storage deque) internal view returns (uint256) {
        unchecked {
            return uint256(deque._end - deque._begin);
        }
    }

    function empty(Bytes32Deque storage deque) internal view returns (bool) {
        return deque._end == deque._begin;
    }
}

abstract contract ContextSlice41 {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

contract SequenceFixture is ContextSlice41 {
    using DoubleEndedQueueSlice41 for DoubleEndedQueueSlice41.Bytes32Deque;

    error GovernorOnlyExecutor(address account);

    event GovernanceCreate2ClonesRecorded(
        address indexed create2Addr,
        address indexed cloneAddr,
        bytes32 msgDataHash,
        uint256 remainingQueue,
        uint256 votingDelay
    );

    DoubleEndedQueueSlice41.Bytes32Deque private _governanceCall;
    DoubleEndedQueueSlice41.Bytes32Deque private _backQueue;
    address private _lockedExecutor;
    uint256 private _votingDelay;
    uint256 private _totalDerivedScore;
    bytes32 private _lastMsgDataHash;

    modifier onlyGovernance() {
        _checkGovernance();
        _;
    }

    function _executor() internal view virtual returns (address) {
        return _lockedExecutor == address(0) ? _msgSender() : _lockedExecutor;
    }

    function _checkGovernance() internal virtual {
        if (_executor() != _msgSender()) {
            revert GovernorOnlyExecutor(_msgSender());
        }
        if (_executor() != address(this)) {
            bytes32 msgDataHash = keccak256(_msgData());
            while (_governanceCall.popFront() != msgDataHash) {}
        }
    }

    function computeCreate2(
        bytes32 salt,
        bytes32 bytecodeHash,
        address deployer
    ) public view returns (address, address) {
        return (
            Create2Slice41.computeAddress(salt, bytecodeHash, deployer),
            Create2Slice41.computeAddress(salt, bytecodeHash)
        );
    }

    function predictClone(
        address implementation,
        bytes32 salt,
        address deployer
    ) public view returns (address, address) {
        return (
            ClonesSlice41.predictDeterministicAddress(implementation, salt, deployer),
            ClonesSlice41.predictDeterministicAddress(implementation, salt)
        );
    }

    function currentMsgDataHash(uint256 tag) public view returns (bytes32) {
        return keccak256(_msgData()) ^ bytes32(tag);
    }

    function executeGovernanceAction(uint256 newVotingDelay) public onlyGovernance returns (uint256) {
        _votingDelay = newVotingDelay;
        _lastMsgDataHash = keccak256(_msgData());
        return _votingDelay;
    }

    function queueLength() public view returns (uint256, uint256) {
        return (_governanceCall.length(), _backQueue.length());
    }

    function change(uint256 input) external returns (uint256) {
        bytes32 salt = keccak256(abi.encode("SALT", input, _votingDelay));
        bytes32 initHash = keccak256(abi.encode("INIT", input, _msgSender()));
        address deployer = address(uint160(0x11110000 + (input & 0xffff)));
        address impl = address(uint160(0x22220000 + ((input >> 4) & 0xffff)));

        address c2Custom = Create2Slice41.computeAddress(salt, initHash, deployer);
        address c2Self = Create2Slice41.computeAddress(salt, initHash);
        address cloneCustom = ClonesSlice41.predictDeterministicAddress(impl, salt, deployer);
        address cloneSelf = ClonesSlice41.predictDeterministicAddress(impl, salt);

        bytes32 cHash = keccak256(_msgData());
        bytes32 leadNoise = keccak256(abi.encode(c2Custom, cloneCustom, uint256(1)));
        bytes32 tailKeep = keccak256(abi.encode(c2Self, cloneSelf, uint256(2)));
        bytes32 govActionHash = keccak256(
            abi.encodeWithSelector(this.executeGovernanceAction.selector, uint256(42))
        );

        _governanceCall.clear();
        _governanceCall.pushBack(leadNoise);
        _governanceCall.pushBack(cHash);
        _governanceCall.pushBack(tailKeep);
        _governanceCall.pushBack(govActionHash);

        _checkGovernance();

        bytes32 poppedTail = _governanceCall.popFront();
        require(poppedTail == tailKeep, "CCMD: governance popFront mismatch");

        _backQueue.clear();
        bytes32 backKeep = keccak256(abi.encode("BACK_KEEP", input));
        bytes32 backTarget = keccak256(abi.encode("BACK_TARGET", cHash));
        bytes32 backNoise = keccak256(abi.encode("BACK_NOISE", salt));
        _backQueue.pushFront(backNoise);
        _backQueue.pushFront(backTarget);
        _backQueue.pushFront(backKeep);

        while (backTarget != _backQueue.popBack()) {}

        uint256 remGov = _governanceCall.length();
        uint256 remBack = _backQueue.length();
        require(remGov == 1 && remBack == 1, "CCMD: unexpected queue lengths");
        require(_backQueue.front() == backKeep, "CCMD: unexpected backQueue front");

        if ((input & 1) == 0) {
            _votingDelay = (input & 0xff) + 10;
        } else {
            _votingDelay = ((input >> 2) & 0xff) + 20;
        }

        uint256 remTotal = remGov + remBack;
        emit GovernanceCreate2ClonesRecorded(c2Custom, cloneCustom, cHash, remTotal, _votingDelay);

        unchecked {
            _totalDerivedScore +=
                (uint256(uint160(c2Custom)) & 0xffff) +
                (uint256(uint160(c2Self)) & 0xffff) +
                (uint256(uint160(cloneCustom)) & 0xffff) +
                (uint256(uint160(cloneSelf)) & 0xffff) +
                _votingDelay +
                remGov +
                remBack;
        }
        _lastMsgDataHash = cHash ^ bytes32(uint256(uint160(c2Self))) ^ bytes32(uint256(uint160(cloneSelf)));
        require(input != 20, "CCMD: rollback");
        return _totalDerivedScore;
    }

    function fail() external {
        _votingDelay += 999;
        _totalDerivedScore += 888;
        revert("CCMD: fail");
    }

    function read() external view returns (uint256, bytes32, uint256, uint256) {
        return (
            _totalDerivedScore,
            _lastMsgDataHash,
            _votingDelay,
            _governanceCall.length() + _backQueue.length()
        );
    }
}
