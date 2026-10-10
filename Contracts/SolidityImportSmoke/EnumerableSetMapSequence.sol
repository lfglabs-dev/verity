// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library StorageSlot {
    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
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
    function unsafeAccess(bytes32[] storage arr, uint256 pos) internal pure returns (StorageSlot.Bytes32Slot storage r) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return StorageSlot.getBytes32Slot(slot);
    }

    function unsafeAccess(uint256[] storage arr, uint256 pos) internal pure returns (StorageSlot.Uint256Slot storage r) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return StorageSlot.getUint256Slot(slot);
    }
}

library EnumerableSet {
    struct Set {
        bytes32[] _values;
        mapping(bytes32 => uint256) _positions;
    }

    struct Bytes32Set {
        Set _inner;
    }

    struct AddressSet {
        Set _inner;
    }

    struct UintSet {
        Set _inner;
    }

    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            set._positions[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    function _remove(Set storage set, bytes32 value) private returns (bool) {
        uint256 position = set._positions[value];

        if (position != 0) {
            uint256 valueIndex = position - 1;
            uint256 lastIndex = set._values.length - 1;

            if (valueIndex != lastIndex) {
                bytes32 lastValue = Arrays.unsafeAccess(set._values, lastIndex).value;
                Arrays.unsafeAccess(set._values, valueIndex).value = lastValue;
                set._positions[lastValue] = position;
            }

            set._values.pop();
            delete set._positions[value];

            return true;
        } else {
            return false;
        }
    }

    function _clear(Set storage set) private {
        uint256 len = set._values.length;
        for (uint256 i = 0; i < len; ++i) {
            delete set._positions[Arrays.unsafeAccess(set._values, i).value];
        }
        delete set._values;
    }

    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._positions[value] != 0;
    }

    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        return set._values[index];
    }

    function _values(Set storage set) private view returns (bytes32[] memory) {
        return set._values;
    }

    // Bytes32Set
    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    function clear(Bytes32Set storage set) internal {
        _clear(set._inner);
    }

    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }

    function values(Bytes32Set storage set) internal view returns (bytes32[] memory) {
        return _values(set._inner);
    }

    // AddressSet
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    function clear(AddressSet storage set) internal {
        _clear(set._inner);
    }

    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint160(uint256(_at(set._inner, index))));
    }

    // UintSet
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    function clear(UintSet storage set) internal {
        _clear(set._inner);
    }

    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }

    function values(UintSet storage set) internal view returns (uint256[] memory) {
        bytes32[] memory store = _values(set._inner);
        uint256[] memory result;
        assembly ("memory-safe") {
            result := store
        }
        return result;
    }
}

library EnumerableMap {
    using EnumerableSet for EnumerableSet.Bytes32Set;

    error EnumerableMapNonexistentKey(bytes32 key);

    struct Bytes32ToBytes32Map {
        EnumerableSet.Bytes32Set _keys;
        mapping(bytes32 => bytes32) _values;
    }

    struct AddressToUintMap {
        Bytes32ToBytes32Map _inner;
    }

    function set(Bytes32ToBytes32Map storage map, bytes32 key, bytes32 value) internal returns (bool) {
        map._values[key] = value;
        return map._keys.add(key);
    }

    function remove(Bytes32ToBytes32Map storage map, bytes32 key) internal returns (bool) {
        delete map._values[key];
        return map._keys.remove(key);
    }

    function clear(Bytes32ToBytes32Map storage map) internal {
        uint256 len = length(map);
        for (uint256 i = 0; i < len; ++i) {
            delete map._values[map._keys.at(i)];
        }
        map._keys.clear();
    }

    function contains(Bytes32ToBytes32Map storage map, bytes32 key) internal view returns (bool) {
        return map._keys.contains(key);
    }

    function length(Bytes32ToBytes32Map storage map) internal view returns (uint256) {
        return map._keys.length();
    }

    function at(Bytes32ToBytes32Map storage map, uint256 index) internal view returns (bytes32 key, bytes32 value) {
        bytes32 atKey = map._keys.at(index);
        return (atKey, map._values[atKey]);
    }

    function tryGet(Bytes32ToBytes32Map storage map, bytes32 key) internal view returns (bool exists, bytes32 value) {
        bytes32 val = map._values[key];
        if (val == bytes32(0)) {
            return (contains(map, key), bytes32(0));
        } else {
            return (true, val);
        }
    }

    function get(Bytes32ToBytes32Map storage map, bytes32 key) internal view returns (bytes32) {
        bytes32 value = map._values[key];
        if (value == 0 && !contains(map, key)) {
            revert EnumerableMapNonexistentKey(key);
        }
        return value;
    }

    // AddressToUintMap
    function set(AddressToUintMap storage map, address key, uint256 value) internal returns (bool) {
        return set(map._inner, bytes32(uint256(uint160(key))), bytes32(value));
    }

    function remove(AddressToUintMap storage map, address key) internal returns (bool) {
        return remove(map._inner, bytes32(uint256(uint160(key))));
    }

    function clear(AddressToUintMap storage map) internal {
        clear(map._inner);
    }

    function contains(AddressToUintMap storage map, address key) internal view returns (bool) {
        return contains(map._inner, bytes32(uint256(uint160(key))));
    }

    function length(AddressToUintMap storage map) internal view returns (uint256) {
        return length(map._inner);
    }

    function at(AddressToUintMap storage map, uint256 index) internal view returns (address key, uint256 value) {
        (bytes32 k, bytes32 v) = at(map._inner, index);
        return (address(uint160(uint256(k))), uint256(v));
    }

    function tryGet(AddressToUintMap storage map, address key) internal view returns (bool exists, uint256 value) {
        (bool ok, bytes32 v) = tryGet(map._inner, bytes32(uint256(uint160(key))));
        return (ok, uint256(v));
    }

    function get(AddressToUintMap storage map, address key) internal view returns (uint256) {
        return uint256(get(map._inner, bytes32(uint256(uint160(key)))));
    }
}

contract SequenceFixture {
    using EnumerableSet for EnumerableSet.AddressSet;
    using EnumerableSet for EnumerableSet.UintSet;
    using EnumerableSet for EnumerableSet.Bytes32Set;
    using EnumerableMap for EnumerableMap.AddressToUintMap;

    error RegistryStepBlocked(uint256 input, bytes32 digest, uint256 setLen);
    event RegistryStepObserved(uint256 indexed totalScore, bytes32 digest, uint256 setLen);

    // ERC-7201 style raw storage slot for CreditRegistryStorage
    bytes32 private constant REGISTRY_STORAGE_LOCATION =
        0x3b8dc3e6d68702fd84e7c6d2c361d9a399fa5bf456e335bd3726c2d3f0392300;

    struct TrancheBucket {
        uint256 weight;
        uint64[] checkpoints;
        mapping(address => uint256) shares;
    }

    struct CreditRegistryStorage {
        uint256 epoch;
        EnumerableSet.AddressSet borrowerSet;
        EnumerableMap.AddressToUintMap creditLimits;
        uint64[] feeSchedule;
        mapping(bytes32 => uint256) facilityAllowances;
    }

    EnumerableSet.UintSet private activeTrancheIds;
    uint256[] private historyLog;
    uint64[] private packedRates;
    mapping(uint256 => TrancheBucket) private buckets;
    uint256 private totalScore;
    bytes32 private lastDigest;

    function _getRegistryStorage() private pure returns (CreditRegistryStorage storage $) {
        assembly ("memory-safe") {
            $.slot := REGISTRY_STORAGE_LOCATION
        }
    }

    function _pushAndAdjustRate(uint64[] storage arr, uint64 baseRate) private {
        arr.push(baseRate);
        uint256 last = arr.length - 1;
        arr[last] += 3;
        arr[last]++;
        arr.push(baseRate + 9);
        arr.pop();
    }

    function change(uint256 input) external returns (uint256) {
        CreditRegistryStorage storage $ = _getRegistryStorage();
        uint256 branch = input % 6;
        address acct1 = address(uint160(0x1000 | (input & 0x3)));
        address acct2 = address(uint160(0x2000 | ((input >> 1) & 0x3)));
        bytes32 fac = bytes32(uint256(0xabc0 | (input & 0x3)));
        uint256 bucketId = input & 0x1;

        if (branch == 0) {
            ++$.epoch;
            $.borrowerSet.add(acct1);
            $.creditLimits.set(acct1, (input & 0xff) | 0x100);
            $.facilityAllowances[fac] += (input & 0x3f) | 0x40;
            _pushAndAdjustRate($.feeSchedule, uint64((input & 0x3f) | 0x10));
            activeTrancheIds.add((input & 0x3) | 0x10);
            historyLog.push((input & 0xffff) | 0x10000);
        } else if (branch == 1) {
            _pushAndAdjustRate(packedRates, uint64((input & 0x3f) | 0x20));
            activeTrancheIds.add(((input >> 2) & 0x3) | 0x10);
            uint256 slotRef = historyLog.push();
            require(slotRef == 0, "default push must be zero");
            historyLog[historyLog.length - 1] = (input & 0xff) | 0x200;
            TrancheBucket storage b = buckets[bucketId];
            b.weight += (input & 0x3f) | 0x1;
            b.checkpoints.push(uint64((input & 0x3f) | 0x30));
            b.shares[acct1] += (input & 0x1f) | 0x4;
        } else if (branch == 2) {
            $.borrowerSet.remove(acct1);
            $.creditLimits.remove(acct1);
            if (packedRates.length > 0) {
                packedRates[0] ^= uint64(input & 0x1f);
                if (packedRates.length > 1) {
                    packedRates.pop();
                }
            }
            if (historyLog.length > 0) {
                Arrays.unsafeAccess(historyLog, 0).value += 11;
                if (historyLog.length > 1) {
                    delete historyLog[0];
                    historyLog.pop();
                }
            }
            TrancheBucket storage b = buckets[bucketId];
            if (b.checkpoints.length > 0) {
                b.checkpoints[b.checkpoints.length - 1] += 5;
            }
            ++b.shares[acct2];
        } else if (branch == 3) {
            (bool hasAcct2, uint256 lim2) = $.creditLimits.tryGet(acct2);
            if (hasAcct2) {
                uint256 exact = $.creditLimits.get(acct2);
                require(exact == lim2, "EnumerableMap get/tryGet mismatch");
                $.creditLimits.set(acct2, lim2 + 15);
            } else {
                $.creditLimits.set(acct2, 0);
                (bool hasZero, uint256 zeroLim) = $.creditLimits.tryGet(acct2);
                require(hasZero && zeroLim == 0, "EnumerableMap zero value must exist");
            }
        } else if (branch == 4) {
            activeTrancheIds.remove((input & 0x3) | 0x10);
            if ($.feeSchedule.length > 0) {
                delete $.feeSchedule[0];
                if ($.feeSchedule.length > 2) {
                    $.feeSchedule.pop();
                }
            }
            delete $.facilityAllowances[fac];
            uint256 mapLen = $.creditLimits.length();
            if (mapLen > 0) {
                (address k0, uint256 v0) = $.creditLimits.at(0);
                historyLog.push((uint256(uint160(k0)) & 0xffff) + v0 + mapLen);
            }
        } else {
            $.borrowerSet.clear();
            $.creditLimits.clear();
            delete packedRates;
            delete buckets[bucketId].checkpoints;
        }

        uint256[] memory trancheSnapshot = activeTrancheIds.values();
        uint256 snapSum = 0;
        if (trancheSnapshot.length > 0) {
            snapSum += trancheSnapshot[0];
        }

        uint256 bLen = $.borrowerSet.length();
        address firstBorrower = bLen > 0 ? $.borrowerSet.at(0) : address(0);
        uint256 cLen = $.creditLimits.length();
        (, uint256 lim1) = $.creditLimits.tryGet(acct1);
        uint256 tLen = activeTrancheIds.length();
        uint256 summary = $.epoch;
        unchecked {
            summary += bLen + cLen + lim1 + tLen + snapSum;
            if (tLen > 0) {
                summary += activeTrancheIds.at(0);
            }
            summary += historyLog.length;
            if (historyLog.length > 0) {
                summary += historyLog[historyLog.length - 1];
            }
            summary += packedRates.length;
            if (packedRates.length > 0) {
                summary += uint256(packedRates[packedRates.length - 1]);
            }
            summary += $.feeSchedule.length;
            if ($.feeSchedule.length > 0) {
                summary += uint256($.feeSchedule[$.feeSchedule.length - 1]);
            }
            summary +=
                buckets[bucketId].weight +
                buckets[bucketId].checkpoints.length +
                buckets[bucketId].shares[acct1] +
                buckets[bucketId].shares[acct2] +
                $.facilityAllowances[fac];
            if (buckets[bucketId].checkpoints.length > 0) {
                summary += uint256(buckets[bucketId].checkpoints[buckets[bucketId].checkpoints.length - 1]);
            }
        }

        bytes32 digest = bytes32(
            (summary << 32) ^
            (bLen << 16) ^
            (cLen << 8) ^
            tLen ^
            uint256(uint160(firstBorrower))
        );

        if (input == 21) {
            revert RegistryStepBlocked(input, digest, bLen);
        }

        uint256 metric = (uint256(digest) & 0xffffffff) + summary;
        totalScore += metric;
        lastDigest = digest;
        emit RegistryStepObserved(totalScore, digest, bLen);
        require(input != 20, "enumerable rollback");
        return totalScore;
    }

    function trancheHistorySnapshot(uint256 mode) external returns (uint256, uint256) {
        CreditRegistryStorage storage $ = _getRegistryStorage();
        if (mode == 99) {
            // Nonexistent key revert path in EnumerableMap.get
            uint256 impossible = $.creditLimits.get(address(0xdeadbeef));
            historyLog.push(impossible);
        } else if (mode == 98) {
            // Empty pop panic 0x31 path
            delete packedRates;
            packedRates.pop();
        } else if (mode == 97) {
            // Out-of-bounds storage dynamic array panic 0x32 path
            uint256 bad = historyLog[historyLog.length];
            historyLog.push(bad);
        }
        uint256 acc = 0;
        if (mode % 2 == 0) {
            activeTrancheIds.add((mode & 0xff) + 10);
            uint256[] memory snap = activeTrancheIds.values();
            for (uint256 i = 0; i < snap.length; ++i) {
                unchecked {
                    acc += snap[i] * (i + 1);
                }
            }
            return (snap.length, acc);
        } else {
            historyLog.push((mode & 0xffff) + 100);
            uint256[] memory snap = historyLog;
            for (uint256 i = 0; i < snap.length; ++i) {
                unchecked {
                    acc += snap[i] * (i + 1);
                }
            }
            return (snap.length, acc);
        }
    }

    function fail() external {
        CreditRegistryStorage storage $ = _getRegistryStorage();
        $.borrowerSet.add(address(0x9999));
        packedRates.push(77);
        historyLog.push(888);
        bytes32 digest = lastDigest;
        uint256 bLen = $.borrowerSet.length();
        revert RegistryStepBlocked(999, digest, bLen);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        CreditRegistryStorage storage $ = _getRegistryStorage();
        uint256 summary;
        unchecked {
            summary =
                $.epoch +
                $.borrowerSet.length() +
                $.creditLimits.length() +
                activeTrancheIds.length() +
                historyLog.length +
                packedRates.length +
                $.feeSchedule.length +
                buckets[0].weight +
                buckets[0].checkpoints.length +
                buckets[1].weight +
                buckets[1].checkpoints.length;
        }
        return (totalScore, lastDigest, summary);
    }
}
