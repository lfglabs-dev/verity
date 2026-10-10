// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library Math {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + (a ^ b) / 2;
    }
}

library SafeCast {
    error SafeCastOverflowedUintDowncast(uint8 bits, uint256 value);

    function toUint208(uint256 value) internal pure returns (uint208) {
        if (value > type(uint208).max) {
            revert SafeCastOverflowedUintDowncast(208, value);
        }
        return uint208(value);
    }

    function toUint48(uint256 value) internal pure returns (uint48) {
        if (value > type(uint48).max) {
            revert SafeCastOverflowedUintDowncast(48, value);
        }
        return uint48(value);
    }
}

library StorageSlot {
    struct AddressSlot {
        address value;
    }

    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }
}

library Arrays {
    using StorageSlot for bytes32;

    function findUpperBound(uint256[] storage array, uint256 element) internal view returns (uint256) {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = Math.average(low, high);

            if (unsafeAccess(array, mid).value > element) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        if (low > 0 && unsafeAccess(array, low - 1).value == element) {
            return low - 1;
        } else {
            return low;
        }
    }

    function unsafeAccess(address[] storage arr, uint256 pos) internal pure returns (StorageSlot.AddressSlot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getAddressSlot();
    }

    function unsafeAccess(bytes32[] storage arr, uint256 pos) internal pure returns (StorageSlot.Bytes32Slot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getBytes32Slot();
    }

    function unsafeAccess(uint256[] storage arr, uint256 pos) internal pure returns (StorageSlot.Uint256Slot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getUint256Slot();
    }
}

library BitMaps {
    struct BitMap {
        mapping(uint256 => uint256) _data;
    }

    function get(BitMap storage bitmap, uint256 index) internal view returns (bool) {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        return bitmap._data[bucket] & mask != 0;
    }

    function setTo(BitMap storage bitmap, uint256 index, bool value) internal {
        if (value) {
            set(bitmap, index);
        } else {
            unset(bitmap, index);
        }
    }

    function set(BitMap storage bitmap, uint256 index) internal {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        bitmap._data[bucket] |= mask;
    }

    function unset(BitMap storage bitmap, uint256 index) internal {
        uint256 bucket = index >> 8;
        uint256 mask = 1 << (index & 0xff);
        bitmap._data[bucket] &= ~mask;
    }
}

library Checkpoints {
    error CheckpointUnorderedInsertion();

    struct Trace208 {
        Checkpoint208[] _checkpoints;
    }

    struct Checkpoint208 {
        uint48 _key;
        uint208 _value;
    }

    function push(
        Trace208 storage self,
        uint48 key,
        uint208 value
    ) internal returns (uint208, uint208) {
        return _insert(self._checkpoints, key, value);
    }

    function lowerLookup(Trace208 storage self, uint48 key) internal view returns (uint208) {
        uint256 len = self._checkpoints.length;
        uint256 pos = _lowerBinaryLookup(self._checkpoints, key, 0, len);
        return pos == len ? 0 : _unsafeAccess(self._checkpoints, pos)._value;
    }

    function upperLookup(Trace208 storage self, uint48 key) internal view returns (uint208) {
        uint256 len = self._checkpoints.length;
        uint256 pos = _upperBinaryLookup(self._checkpoints, key, 0, len);
        return pos == 0 ? 0 : _unsafeAccess(self._checkpoints, pos - 1)._value;
    }

    function upperLookupRecent(Trace208 storage self, uint48 key) internal view returns (uint208) {
        uint256 len = self._checkpoints.length;
        uint256 pos = _upperBinaryLookup(self._checkpoints, key, 0, len);
        return pos == 0 ? 0 : _unsafeAccess(self._checkpoints, pos - 1)._value;
    }

    function latest(Trace208 storage self) internal view returns (uint208) {
        uint256 pos = self._checkpoints.length;
        return pos == 0 ? 0 : _unsafeAccess(self._checkpoints, pos - 1)._value;
    }

    function latestCheckpoint(Trace208 storage self) internal view returns (bool exists, uint48 _key, uint208 _value) {
        uint256 pos = self._checkpoints.length;
        if (pos == 0) {
            return (false, 0, 0);
        } else {
            Checkpoint208 memory ckpt = _unsafeAccess(self._checkpoints, pos - 1);
            return (true, ckpt._key, ckpt._value);
        }
    }

    function length(Trace208 storage self) internal view returns (uint256) {
        return self._checkpoints.length;
    }

    function at(Trace208 storage self, uint32 pos) internal view returns (Checkpoint208 memory) {
        return self._checkpoints[pos];
    }

    function _insert(
        Checkpoint208[] storage self,
        uint48 key,
        uint208 value
    ) private returns (uint208, uint208) {
        uint256 pos = self.length;

        if (pos > 0) {
            Checkpoint208 memory last = _unsafeAccess(self, pos - 1);
            uint48 lastKey = last._key;
            uint208 lastValue = last._value;

            if (lastKey > key) {
                revert CheckpointUnorderedInsertion();
            }

            if (lastKey == key) {
                _unsafeAccess(self, pos - 1)._value = value;
                return (lastValue, value);
            }
        }

        self.push(Checkpoint208({_key: key, _value: value}));
        return (pos == 0 ? 0 : _unsafeAccess(self, pos - 1)._value, value);
    }

    function _upperBinaryLookup(
        Checkpoint208[] storage self,
        uint48 key,
        uint256 low,
        uint256 high
    ) private view returns (uint256) {
        while (low < high) {
            uint256 mid = Math.average(low, high);
            if (_unsafeAccess(self, mid)._key > key) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        return high;
    }

    function _lowerBinaryLookup(
        Checkpoint208[] storage self,
        uint48 key,
        uint256 low,
        uint256 high
    ) private view returns (uint256) {
        while (low < high) {
            uint256 mid = Math.average(low, high);
            if (_unsafeAccess(self, mid)._key < key) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        return high;
    }

    function _unsafeAccess(
        Checkpoint208[] storage self,
        uint256 pos
    ) private pure returns (Checkpoint208 storage result) {
        assembly {
            mstore(0, self.slot)
            result.slot := add(keccak256(0, 0x20), pos)
        }
    }
}

contract SequenceFixture {
    using Checkpoints for Checkpoints.Trace208;
    using Arrays for uint256[];
    using Arrays for address[];
    using Arrays for bytes32[];
    using BitMaps for BitMaps.BitMap;

    error VotesStepBlocked(uint256 input, bytes32 digest, uint256 totalCkpts);
    event DelegateVotesChanged(address indexed delegate, uint256 previousVotes, uint256 newVotes);

    mapping(address => address) private _delegatee;
    mapping(address => Checkpoints.Trace208) private _delegateCheckpoints;
    Checkpoints.Trace208 private _totalCheckpoints;

    uint256[] private _snapshots;
    address[] private _signers;
    bytes32[] private _tags;
    BitMaps.BitMap private _claimed;

    address private _pendingDefaultAdmin;
    uint48 private _pendingDefaultAdminSchedule;

    mapping(bool => address) public roleSetter;
    mapping(bool => mapping(address => bool)) public isWhitelister;
    mapping(bool => mapping(address => mapping(address => uint256))) public nonces;

    uint256 private totalScore;
    bytes32 private lastDigest;

    function clock() public view returns (uint48) {
        return SafeCast.toUint48(block.timestamp);
    }

    function _add(uint208 a, uint208 b) private pure returns (uint208) {
        return a + b;
    }

    function _subtract(uint208 a, uint208 b) private pure returns (uint208) {
        return a - b;
    }

    function _push(
        Checkpoints.Trace208 storage store,
        function(uint208, uint208) view returns (uint208) op,
        uint208 delta
    ) private returns (uint208 oldValue, uint208 newValue) {
        return store.push(clock(), op(store.latest(), delta));
    }

    function _checkOp(
        Checkpoints.Trace208 storage store,
        function(uint208, uint208) view returns (uint208) op,
        uint208 delta
    ) private view {
        op(store.latest(), delta);
    }

    function _applyOp(
        Checkpoints.Trace208 storage store,
        function(uint208, uint208) view returns (uint208) op,
        uint208 delta
    ) private returns (uint208) {
        _checkOp(store, op, delta);
        (, uint208 updated) = _push(store, op, delta);
        return updated;
    }

    function _moveDelegateVotes(address from, address to, uint256 amount) private {
        if (from != to && amount > 0) {
            if (from != address(0)) {
                (uint256 oldValue, uint256 newValue) = _push(
                    _delegateCheckpoints[from],
                    _subtract,
                    SafeCast.toUint208(amount)
                );
                emit DelegateVotesChanged(from, oldValue, newValue);
            }
            if (to != address(0)) {
                (uint256 oldValue, uint256 newValue) = _push(
                    _delegateCheckpoints[to],
                    _add,
                    SafeCast.toUint208(amount)
                );
                emit DelegateVotesChanged(to, oldValue, newValue);
            }
        }
    }

    function _transferVotingUnits(address from, address to, uint256 amount) private {
        if (from == address(0)) {
            _push(_totalCheckpoints, _add, SafeCast.toUint208(amount));
        }
        if (to == address(0)) {
            _push(_totalCheckpoints, _subtract, SafeCast.toUint208(amount));
        }
        _moveDelegateVotes(_delegatee[from], _delegatee[to], amount);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 branch = input % 4;
        address voter = address(uint160(0x3000 | (input & 0x3)));
        address delegatee = address(uint160(0x4000 | ((input >> 2) & 0x3)));
        uint256 amount = ((input & 0x3f) + 1) * 10;
        uint256 snapKey = _snapshots.length * 100 + (input & 0x1f);

        if (branch == 0) {
            _delegatee[voter] = delegatee;
            _transferVotingUnits(address(0), voter, amount);
            _snapshots.push(snapKey);
            _signers.push(delegatee);
            _tags.push(bytes32((snapKey << 16) ^ uint256(uint160(voter))));
            _claimed.setTo(input & 0x1ff, true);
            roleSetter[true] = msg.sender;
            isWhitelister[true][delegatee] = true;
            nonces[true][voter][delegatee] += 1;
        } else if (branch == 1) {
            uint208 curVotes = _delegateCheckpoints[delegatee].latest();
            bool canSub = curVotes >= uint208(amount / 2) && (input & 1) == 1;
            function(uint208, uint208) view returns (uint208) chosenOp = canSub ? _subtract : _add;
            _applyOp(_delegateCheckpoints[delegatee], chosenOp, uint208(amount / 2));
            _claimed.setTo(input & 0x1ff, !canSub);
            roleSetter[false] = voter;
            isWhitelister[false][delegatee] = canSub;
            nonces[false][voter][delegatee] += 2;
        } else if (branch == 2) {
            _pendingDefaultAdmin = delegatee;
            _pendingDefaultAdminSchedule = (input & 1) == 0 ? clock() + 3600 : 0;
            _snapshots.push(snapKey);
            _signers.push(voter);
            _tags.push(bytes32(amount));
        } else {
            _claimed.set(input & 0xff);
            if ((input & 2) != 0) {
                _claimed.unset(input & 0xff);
            }
        }

        address firstSigner = _signers.length > 0 ? _signers.unsafeAccess(0).value : address(0);
        bytes32 firstTag = _tags.length > 0 ? _tags.unsafeAccess(0).value : bytes32(0);
        uint256 firstSnap = _snapshots.length > 0 ? _snapshots.unsafeAccess(0).value : 0;

        (bool hasTotal, uint48 latestKey, uint208 latestTotal) = _totalCheckpoints.latestCheckpoint();
        uint208 delLatest = _delegateCheckpoints[delegatee].latest();
        (address pendAdmin, uint48 pendSched) = pendingDefaultAdminView();

        uint256 summary;
        unchecked {
            summary =
                uint256(uint160(firstSigner)) +
                (uint256(firstTag) & 0xffff) +
                firstSnap +
                (hasTotal ? 1 : 0) +
                uint256(latestKey) +
                uint256(latestTotal) +
                uint256(delLatest) +
                uint256(uint160(pendAdmin)) +
                uint256(pendSched) +
                (_claimed.get(input & 0x1ff) ? 1 : 0) +
                uint256(uint160(roleSetter[true])) +
                (isWhitelister[true][delegatee] ? 1 : 0) +
                nonces[true][voter][delegatee] +
                nonces[false][voter][delegatee];
        }

        uint256 cLen = _totalCheckpoints.length();
        bytes32 digest = bytes32(
            (summary << 32) ^
            (cLen << 16) ^
            (_snapshots.length << 8) ^
            uint256(delLatest)
        );

        if (input == 21) {
            revert VotesStepBlocked(input, digest, cLen);
        }

        uint256 metric = (uint256(digest) & 0xffffffff) + summary;
        totalScore += metric;
        lastDigest = digest;
        require(input != 20, "votes rollback");
        return totalScore;
    }

    function pendingDefaultAdminView() public view returns (address newAdmin, uint48 schedule) {
        return _pendingDefaultAdminSchedule > 0
            ? (_pendingDefaultAdmin, _pendingDefaultAdminSchedule)
            : (address(0), 0);
    }

    function checkpoints(address account, uint32 pos) external view returns (Checkpoints.Checkpoint208 memory) {
        return _delegateCheckpoints[account].at(pos);
    }

    function latestTotalCheckpoint() external view returns (Checkpoints.Checkpoint208 memory) {
        uint256 len = _totalCheckpoints.length();
        return len > 0
            ? _totalCheckpoints.at(uint32(len - 1))
            : Checkpoints.Checkpoint208({_key: 0, _value: 0});
    }

    function voteWindow(uint256 targetSnap, uint256 mode) external returns (uint256, uint256) {
        address delegatee = address(uint160(0x4000 | (targetSnap & 0x3)));
        if (mode == 99) {
            uint208 bad = SafeCast.toUint208(uint256(type(uint208).max) + 1);
            return (uint256(bad), 0);
        } else if (mode == 98) {
            Checkpoints.Checkpoint208 memory oob = _totalCheckpoints.at(uint32(_totalCheckpoints.length()));
            return (uint256(oob._key), uint256(oob._value));
        } else if (mode == 97) {
            uint208 cur = _delegateCheckpoints[delegatee].latest();
            _checkOp(_delegateCheckpoints[delegatee], _subtract, cur + 1);
            return (uint256(cur), 1);
        }
        uint256 ub = _snapshots.findUpperBound(targetSnap);
        uint208 up = _totalCheckpoints.upperLookup(clock());
        uint208 low = _delegateCheckpoints[delegatee].lowerLookup(clock());
        return (ub + uint256(up), uint256(low));
    }

    function fail() external {
        address voter = address(0x3001);
        _delegatee[voter] = voter;
        _transferVotingUnits(address(0), voter, 500);
        _snapshots.push(777);
        bytes32 digest = lastDigest;
        uint256 cLen = _totalCheckpoints.length();
        revert VotesStepBlocked(999, digest, cLen);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        uint256 summary;
        unchecked {
            summary =
                _totalCheckpoints.length() +
                uint256(_totalCheckpoints.latest()) +
                _snapshots.length +
                _signers.length +
                _tags.length +
                uint256(_pendingDefaultAdminSchedule);
        }
        return (totalScore, lastDigest, summary);
    }
}
