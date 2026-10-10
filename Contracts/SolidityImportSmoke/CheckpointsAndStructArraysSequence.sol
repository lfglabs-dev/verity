// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library Math {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + (a ^ b) / 2;
    }
}

library Checkpoints {
    struct Trace208 {
        Checkpoint208[] _checkpoints;
    }

    struct Checkpoint208 {
        uint48 _key;
        uint208 _value;
    }

    error CheckpointUnorderedInsertion();

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

        uint256 low = 0;
        uint256 high = len;

        if (len > 5) {
            uint256 mid = len - 2;
            if (key < _unsafeAccess(self._checkpoints, mid)._key) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        uint256 pos = _upperBinaryLookup(self._checkpoints, key, low, high);

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

    function clear(Trace208 storage self) internal {
        delete self._checkpoints;
    }

    function _insert(
        Checkpoint208[] storage self,
        uint48 key,
        uint208 value
    ) private returns (uint208, uint208) {
        uint256 pos = self.length;

        if (pos > 0) {
            Checkpoint208 memory last = _unsafeAccess(self, pos - 1);

            if (last._key > key) {
                revert CheckpointUnorderedInsertion();
            }

            if (last._key == key) {
                _unsafeAccess(self, pos - 1)._value = value;
                return (last._value, value);
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

    error CheckpointStepBlocked(uint256 input, bytes32 digest, uint256 ckptLen);
    event CheckpointStepObserved(uint256 indexed totalScore, bytes32 digest, uint256 ckptLen);

    bytes32 private constant GOVERNANCE_STORAGE_LOCATION =
        0x91e52f46fb82f53a45f396cf2b3709c2b2f5a9a23be373602d86e49e8a6b4100;

    struct TrancheRecord {
        uint256 assets;
        uint128 shares;
        uint64 epoch;
        bool locked;
    }

    struct GovernanceStorage {
        uint48 lastClock;
        Checkpoints.Trace208 totalSupplyCheckpoints;
        mapping(address => Checkpoints.Trace208) delegateCheckpoints;
    }

    TrancheRecord[] private trancheRecords;
    Checkpoints.Trace208 private epochCheckpoints;
    uint256 private totalScore;
    bytes32 private lastDigest;

    function _getGovernanceStorage() private pure returns (GovernanceStorage storage $) {
        assembly ("memory-safe") {
            $.slot := GOVERNANCE_STORAGE_LOCATION
        }
    }

    function _makeRecord(uint256 seed, uint64 epoch, bool locked) private pure returns (TrancheRecord memory) {
        return TrancheRecord({
            locked: locked,
            epoch: epoch,
            shares: uint128((seed & 0xffff) + 10),
            assets: (seed & 0xffffff) + 100
        });
    }

    function change(uint256 input) external returns (uint256) {
        GovernanceStorage storage $ = _getGovernanceStorage();
        uint256 branch = input % 6;
        address voter = address(uint160(0x3000 | (input & 0x1)));
        uint48 stepDelta = uint48((input & 0x3) + 1);

        if (branch == 0) {
            uint48 nextClock = $.lastClock + stepDelta;
            $.lastClock = nextClock;
            uint208 nextSupply = $.totalSupplyCheckpoints.latest() + uint208((input & 0xff) + 10);
            $.totalSupplyCheckpoints.push(nextClock, nextSupply);
            $.delegateCheckpoints[voter].push(nextClock, uint208((input & 0x7f) + 5));
            epochCheckpoints.push(nextClock, uint208(nextClock) * 3);
            trancheRecords.push(_makeRecord(input, uint64(nextClock), (input & 1) == 0));
        } else if (branch == 1) {
            uint48 clock = $.lastClock;
            if (clock == 0) {
                clock = 1;
                $.lastClock = 1;
            }
            // Same-key update path in Checkpoints._insert
            (uint208 oldVal, uint208 newVal) = $.totalSupplyCheckpoints.push(
                clock,
                $.totalSupplyCheckpoints.latest() + uint208((input & 0x3f) + 1)
            );
            epochCheckpoints.push(clock, oldVal + newVal + 1);
            TrancheRecord storage pushed = trancheRecords.push();
            pushed.assets = uint256(newVal) + 50;
            pushed.shares = uint128(oldVal) + 7;
            pushed.epoch = uint64(clock);
            pushed.locked = true;
        } else if (branch == 2) {
            if (trancheRecords.length > 0) {
                uint256 lastIdx = trancheRecords.length - 1;
                TrancheRecord memory cur = trancheRecords[lastIdx];
                trancheRecords[0] = TrancheRecord({
                    epoch: cur.epoch + 1,
                    locked: !cur.locked,
                    assets: cur.assets + 17,
                    shares: cur.shares + 3
                });
                if (trancheRecords.length > 1) {
                    delete trancheRecords[lastIdx];
                    trancheRecords.pop();
                }
            }
            uint48 nextClock = $.lastClock + 2;
            $.lastClock = nextClock;
            $.delegateCheckpoints[voter].push(nextClock, uint208((input & 0xff) + 20));
        } else if (branch == 3) {
            // Populate multiple checkpoints to exercise > 5 recent binary search
            for (uint256 i = 0; i < 3; ++i) {
                uint48 k = $.lastClock + uint48(i + 1);
                $.lastClock = k;
                $.totalSupplyCheckpoints.push(k, uint208(k) * 10 + uint208(i));
            }
        } else if (branch == 4) {
            if (epochCheckpoints.length() > 0) {
                Checkpoints.Checkpoint208 memory firstCkpt = epochCheckpoints.at(0);
                uint48 nextClock = $.lastClock + 1;
                $.lastClock = nextClock;
                epochCheckpoints.push(nextClock, firstCkpt._value + uint208(firstCkpt._key));
            }
            if (trancheRecords.length > 0) {
                trancheRecords[0].assets += 9;
                trancheRecords[0].shares += 2;
            }
        } else {
            epochCheckpoints.clear();
            delete trancheRecords;
        }

        uint256 cLen = $.totalSupplyCheckpoints.length();
        (bool hasLatest, uint48 latestKey, uint208 latestVal) = $.totalSupplyCheckpoints.latestCheckpoint();
        uint48 queryKey = latestKey > 1 ? latestKey - 1 : latestKey;
        uint208 recentVal = $.totalSupplyCheckpoints.upperLookupRecent(queryKey);
        uint208 voterVal = $.delegateCheckpoints[voter].latest();

        Checkpoints.Checkpoint208 memory chosen = cLen > 0
            ? $.totalSupplyCheckpoints.at(0)
            : Checkpoints.Checkpoint208({_value: 9, _key: 0});

        uint256 recSum = trancheRecords.length;
        if (trancheRecords.length > 0) {
            TrancheRecord memory r0 = trancheRecords[0];
            unchecked {
                recSum += r0.assets + uint256(r0.shares) + uint256(r0.epoch) + (r0.locked ? 1 : 0);
            }
        }

        uint256 summary = uint256($.lastClock);
        unchecked {
            summary +=
                cLen +
                (hasLatest ? 1 : 0) +
                uint256(latestKey) +
                uint256(latestVal) +
                uint256(recentVal) +
                uint256(voterVal) +
                uint256(chosen._key) +
                uint256(chosen._value) +
                epochCheckpoints.length() +
                uint256(epochCheckpoints.latest()) +
                recSum;
        }

        bytes32 digest = bytes32(
            (summary << 32) ^
            (cLen << 16) ^
            (trancheRecords.length << 8) ^
            uint256(voterVal) ^
            uint256(recentVal)
        );

        if (input == 21) {
            revert CheckpointStepBlocked(input, digest, cLen);
        }

        uint256 metric = (uint256(digest) & 0xffffffff) + summary;
        totalScore += metric;
        lastDigest = digest;
        emit CheckpointStepObserved(totalScore, digest, cLen);
        require(input != 20, "checkpoint rollback");
        return totalScore;
    }

    function lookupWindow(uint48 queryKey, uint256 mode) external returns (uint256, uint256) {
        GovernanceStorage storage $ = _getGovernanceStorage();
        if (mode == 99) {
            // Unordered checkpoint insertion custom error revert path
            uint48 k = $.lastClock + 5;
            $.lastClock = k;
            $.totalSupplyCheckpoints.push(k, 100);
            $.totalSupplyCheckpoints.push(k - 1, 200);
        } else if (mode == 98) {
            // Out-of-bounds struct dynamic array index panic 0x32 path
            Checkpoints.Checkpoint208 memory bad = $.totalSupplyCheckpoints.at(uint32($.totalSupplyCheckpoints.length()));
            return (uint256(bad._key), uint256(bad._value));
        } else if (mode == 97) {
            // Empty struct dynamic array pop panic 0x31 path
            delete trancheRecords;
            trancheRecords.pop();
        }
        uint208 up = $.totalSupplyCheckpoints.upperLookup(queryKey);
        uint208 low = $.totalSupplyCheckpoints.lowerLookup(queryKey);
        return (uint256(up), uint256(low));
    }

    function fail() external {
        GovernanceStorage storage $ = _getGovernanceStorage();
        uint48 k = $.lastClock + 10;
        $.lastClock = k;
        $.totalSupplyCheckpoints.push(k, 777);
        trancheRecords.push(_makeRecord(42, uint64(k), true));
        bytes32 digest = lastDigest;
        uint256 cLen = $.totalSupplyCheckpoints.length();
        revert CheckpointStepBlocked(999, digest, cLen);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        GovernanceStorage storage $ = _getGovernanceStorage();
        uint256 summary;
        unchecked {
            summary =
                uint256($.lastClock) +
                $.totalSupplyCheckpoints.length() +
                uint256($.totalSupplyCheckpoints.latest()) +
                epochCheckpoints.length() +
                uint256(epochCheckpoints.latest()) +
                trancheRecords.length;
        }
        return (totalScore, lastDigest, summary);
    }
}
