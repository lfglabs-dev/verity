// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type ShortString is bytes32;

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

library DoubleEndedQueue {
    error QueueEmpty();
    error QueueFull();
    error QueueOutOfBounds();

    struct Bytes32Deque {
        uint128 _begin;
        uint128 _end;
        mapping(uint128 => bytes32) _data;
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

library ShortStrings {
    bytes32 private constant FALLBACK_SENTINEL =
        0x00000000000000000000000000000000000000000000000000000000000000FF;

    error InvalidShortString();

    function toShortString(string memory str) internal pure returns (ShortString) {
        bytes memory bstr = bytes(str);
        if (bstr.length > 31) {
            revert InvalidShortString();
        }
        return ShortString.wrap(bytes32(uint256(bytes32(bstr)) | bstr.length));
    }

    function byteLength(ShortString s) internal pure returns (uint256) {
        uint256 result = uint256(ShortString.unwrap(s)) & 0xFF;
        if (result > 31) {
            revert InvalidShortString();
        }
        return result;
    }

    function byteLengthWithFallback(ShortString value, string storage store) internal view returns (uint256) {
        uint256 result = uint256(ShortString.unwrap(value)) & 0xFF;
        if (result == 255) {
            return bytes(store).length;
        } else {
            return byteLength(value);
        }
    }
}

contract SequenceFixture {
    using BitMaps for BitMaps.BitMap;
    using DoubleEndedQueue for DoubleEndedQueue.Bytes32Deque;
    using ShortStrings for string;
    using ShortStrings for ShortString;

    struct QueueMeta {
        uint128 weight;
        uint64 epoch;
        bool active;
    }

    error DequeShortStringsRollback();

    event QueueBitmapRecorded(
        uint256 indexed totalScore,
        bytes32 indexed lastHead,
        uint256 queueLen,
        bool bitActive,
        uint256 shortLen
    );

    BitMaps.BitMap private _bitmap;
    DoubleEndedQueue.Bytes32Deque private _primaryDeque;
    mapping(uint256 => DoubleEndedQueue.Bytes32Deque) private _deques;
    mapping(uint256 => QueueMeta) private _metaByQueue;
    string private _fallbackStore;
    ShortString private _lastShort;
    uint256 private totalScore;
    bytes32 private lastHead;
    uint32 private lastTag;

    function _scoreMeta(QueueMeta memory meta) internal pure returns (uint256) {
        return (meta.active ? uint256(meta.weight) * 3 : uint256(meta.weight)) + uint256(meta.epoch);
    }

    function _inspectStore(string storage store) internal view returns (bytes32 word, bytes4 prefix, uint256 len) {
        bytes memory raw = bytes(store);
        word = bytes32(raw);
        prefix = bytes4(raw);
        len = raw.length;
    }

    function dequeAndBitmapStep(string calldata label, uint256 code)
        external
        returns (bytes32, uint256, bool, bytes4)
    {
        uint256 qId = code & 3;
        uint256 bitIdx = (code >> 2) & 0x1ff;
        bool enableBit = (code & 1) == 0;
        _bitmap.setTo(bitIdx, enableBit);

        bytes memory labelBytes = bytes(label);
        ShortString ss;
        if (labelBytes.length < 32) {
            ss = label.toShortString();
        } else {
            _fallbackStore = label;
            ss = ShortString.wrap(bytes32(uint256(0xFF)));
        }
        _lastShort = ss;
        uint256 resolvedLen = ss.byteLengthWithFallback(_fallbackStore);

        bytes32 item = keccak256(abi.encodePacked(label, code, resolvedLen));
        if ((code & 2) == 0) {
            _primaryDeque.pushBack(item);
            _deques[qId].pushFront(item ^ bytes32(code));
        } else {
            _primaryDeque.pushFront(item);
            _deques[qId].pushBack(item ^ bytes32(code));
        }

        bytes32 frontVal = _primaryDeque.front();
        bytes32 backVal = _primaryDeque.back();
        uint256 pLen = _primaryDeque.length();
        bytes32 midVal = _primaryDeque.at(pLen - 1);

        if (pLen > 2) {
            bytes32 popped = (code & 4) == 0 ? _primaryDeque.popFront() : _primaryDeque.popBack();
            frontVal = frontVal ^ popped;
        }
        if ((code & 8) != 0 && !_deques[qId].empty()) {
            _deques[qId].clear();
        }

        _metaByQueue[qId] = QueueMeta(uint128((code & 0xff) + resolvedLen), uint64(pLen), enableBit);
        uint256 metaScore = _scoreMeta(_metaByQueue[qId]);
        bytes4 tag = bytes4(labelBytes) ^ bytes4(frontVal) ^ bytes4(backVal ^ midVal);

        lastHead = frontVal;
        lastTag = uint32(tag);
        bool isSet = _bitmap.get(bitIdx);
        uint256 curLen = _primaryDeque.length();
        totalScore += metaScore + resolvedLen + curLen + (isSet ? 19 : 5);
        emit QueueBitmapRecorded(totalScore, lastHead, curLen, isSet, resolvedLen);
        return (frontVal, totalScore, isSet, tag);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 qId = input & 3;
        uint256 bitIdx = (input >> 2) & 0x3ff;
        if (input == 21) {
            _deques[3].clear();
            _deques[3].popFront();
        }

        if ((input & 1) == 0) {
            _bitmap.set(bitIdx);
        } else {
            _bitmap.set(bitIdx);
            _bitmap.unset(bitIdx);
        }
        bool bitState = _bitmap.get(bitIdx);

        string memory label = (input & 2) == 0 ? "oz-short-queue" : "pareto-bitmap";
        ShortString ss = label.toShortString();
        _lastShort = ss;
        if ((input & 4) == 0) {
            _fallbackStore = "fallback-long-storage-string-value-for-shortstrings";
        } else {
            delete _fallbackStore;
        }
        uint256 sLen = ss.byteLength();
        ShortString sentinel = ShortString.wrap(bytes32(uint256(0xFF)));
        uint256 fbLen = sentinel.byteLengthWithFallback(_fallbackStore);
        (bytes32 storeWord, bytes4 storePrefix, uint256 storeRawLen) = _inspectStore(_fallbackStore);

        bytes32 entry = bytes32(uint256(ShortString.unwrap(ss)) ^ input ^ uint256(storeWord));
        _primaryDeque.pushBack(entry);
        _primaryDeque.pushFront(entry ^ bytes32(uint256(sLen)));
        bytes32 popped = (input & 8) == 0 ? _primaryDeque.popBack() : _primaryDeque.popFront();

        _deques[qId].pushBack(popped);
        bytes32 qFront = _deques[qId].front();
        bytes32 qAt0 = _deques[qId].at(0);
        uint256 qLen = _deques[qId].length();
        if ((input & 16) != 0) {
            _deques[qId].clear();
        }

        uint256 combinedLen = sLen + fbLen;
        QueueMeta memory localMeta = QueueMeta(uint128((input & 0xff) + combinedLen), uint64(qLen + storeRawLen), bitState);
        _metaByQueue[qId] = localMeta;
        uint256 scoreLocal = _scoreMeta(localMeta);
        uint256 scoreStored = _scoreMeta(_metaByQueue[qId]);

        lastHead = qFront ^ qAt0 ^ popped;
        bytes4 tag = storePrefix ^ bytes4(bytes(label)) ^ bytes4(lastHead);
        lastTag = uint32(tag);
        uint256 curLen = _primaryDeque.length();
        totalScore += scoreLocal + scoreStored + curLen + (uint256(lastHead) & 0xffff) + uint256(lastTag & 0xff);

        emit QueueBitmapRecorded(totalScore, lastHead, curLen, bitState, combinedLen);
        require(input != 20, "storage struct params deque shortstrings rollback");
        return totalScore;
    }

    function fail() external {
        _bitmap.set(77);
        _primaryDeque.pushBack(bytes32(uint256(0x1234)));
        totalScore += 999;
        if (msg.sender != address(0)) {
            revert DequeShortStringsRollback();
        }
    }

    function read() external view returns (uint256, bytes32, uint256, bool, bytes4) {
        return (
            totalScore,
            lastHead,
            _primaryDeque.length() + _lastShort.byteLengthWithFallback(_fallbackStore),
            _bitmap.get(0),
            bytes4(lastTag)
        );
    }
}
