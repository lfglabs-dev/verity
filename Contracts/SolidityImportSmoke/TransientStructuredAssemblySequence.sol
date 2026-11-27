// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Structured low-level call helpers: each block is one Yul statement over typed locals.
library LowLevelCallHelpers {
    error FailedCall();

    function staticcallNoReturn(address target, bytes memory data)
        internal
        view
        returns (bool success)
    {
        assembly ("memory-safe") {
            success := staticcall(gas(), target, add(data, 0x20), mload(data), 0x00, 0x00)
        }
    }

    function callNoValue(address target, bytes memory data) internal returns (bool success) {
        assembly ("memory-safe") {
            success := call(gas(), target, 0, add(data, 0x20), mload(data), 0x00, 0x00)
        }
    }

    function callWithValue(address target, uint256 value, bytes memory data)
        internal
        returns (bool success)
    {
        assembly ("memory-safe") {
            success := call(gas(), target, value, add(data, 0x20), mload(data), 0x00, 0x00)
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

    function bubbleRevertData(bytes memory returndata) internal pure {
        assembly ("memory-safe") {
            revert(add(returndata, 0x20), mload(returndata))
        }
    }
}

/// The same block shapes under other names, with the `add(0x20, data)` operand order.
library RenamedCallHelpers {
    function probe(address dst, bytes memory payload) internal view returns (bool ok) {
        assembly ("memory-safe") {
            ok := staticcall(gas(), dst, add(0x20, payload), mload(payload), 0, 0)
        }
    }

    function size() internal pure returns (uint256 n) {
        assembly ("memory-safe") {
            n := returndatasize()
        }
    }
}

/// A transient flag and counter in closures that also run structured low-level call helpers and
/// single-statement transient word accesses at hashed bases `>= 2^128`.
contract TransientStructuredAssemblySequence {
    bytes32 private constant QUEUE_BASE = keccak256("verity.fixture.transient.queue");
    bytes32 private constant TAG_SLOT =
        0x2222222222222222222222222222222222222222222222222222222222222200;
    bytes32 private constant LOW_SLOT = bytes32(uint256(1));

    uint256 private total;
    uint256 private probes;
    bool private transient _locked;
    uint256 private transient _count;

    function _push(uint256 index, uint256 key) private {
        bytes32 base = QUEUE_BASE;
        assembly ("memory-safe") {
            tstore(add(base, and(index, 0xff)), key)
        }
    }

    function _at(uint256 index) private view returns (uint256 key) {
        bytes32 base = QUEUE_BASE;
        assembly ("memory-safe") {
            key := tload(add(and(0xff, index), base))
        }
    }

    function _setTag(bytes32 tag) private {
        assembly ("memory-safe") {
            tstore(TAG_SLOT, tag)
        }
    }

    function _tag() private view returns (bytes32 tag) {
        assembly ("memory-safe") {
            tag := tload(TAG_SLOT)
        }
    }

    function _tagNext() private view returns (uint256 word) {
        assembly ("memory-safe") {
            word := tload(add(TAG_SLOT, 1))
        }
    }

    /// Staticcall under a transient lock; a failed call bubbles its revert data.
    function lockedProbe(address target, bytes calldata payload) external returns (uint256) {
        require(!_locked, "locked");
        _locked = true;
        bool ok = LowLevelCallHelpers.staticcallNoReturn(target, payload);
        if (!ok) {
            if (LowLevelCallHelpers.returnDataSize() > 0) LowLevelCallHelpers.bubbleRevert();
            revert LowLevelCallHelpers.FailedCall();
        }
        uint256 n = LowLevelCallHelpers.returnDataSize();
        probes += 1;
        _locked = false;
        return n;
    }

    function renamedProbe(address target, bytes calldata payload) external returns (uint256) {
        require(!_locked, "locked");
        _locked = true;
        bool ok = RenamedCallHelpers.probe(target, payload);
        uint256 n = RenamedCallHelpers.size();
        probes += ok ? 1 : 0;
        _locked = false;
        return ok ? n : type(uint256).max;
    }

    /// A value-free call as the last interaction, after a transient read.
    function guardedCall(address target, bytes calldata payload) external returns (bool) {
        require(!_locked, "locked");
        bool ok = LowLevelCallHelpers.callNoValue(target, payload);
        if (!ok) {
            if (LowLevelCallHelpers.returnDataSize() > 0) LowLevelCallHelpers.bubbleRevert();
            revert LowLevelCallHelpers.FailedCall();
        }
        return ok;
    }

    /// A value-parameter call with `returnData()` allocation and 1-arg `bubbleRevertData`.
    function guardedCallReturn(address target, uint256 value, bytes calldata payload)
        external
        returns (bytes memory)
    {
        require(!_locked, "locked");
        bool ok = LowLevelCallHelpers.callWithValue(target, value, payload);
        bytes memory ret = LowLevelCallHelpers.returnData();
        if (!ok) {
            if (ret.length > 0) LowLevelCallHelpers.bubbleRevertData(ret);
            revert LowLevelCallHelpers.FailedCall();
        }
        return ret;
    }

    /// Pushes `a` and `b` to the transient queue, then tags and adds the first entry plus the
    /// two new ones.
    function queueSum(uint256 a, uint256 b) external returns (uint256) {
        require(!_locked, "locked");
        _locked = true;
        uint256 count = _count;
        _push(count, a);
        _push(count + 1, b);
        _count = count + 2;
        uint256 sum = _at(0) + _at(count) + _at(count + 1);
        _setTag(bytes32(sum));
        total += uint256(_tag());
        _locked = false;
        return sum;
    }

    /// The index mask: index 256 + i reads the entry at i.
    function queueAt(uint256 index) external view returns (uint256 count, uint256 key, bytes32 tag, uint256 next) {
        return (_count, _at(index), _tag(), _tagNext());
    }

    function queueRevert(uint256 a) external {
        _locked = true;
        _push(_count, a);
        _count += 1;
        _setTag(bytes32(a));
        total += a;
        revert("rollback");
    }

    function state() external view returns (uint256, uint256, bool, uint256) {
        return (total, probes, _locked, _count);
    }

    // ---- Negative controls: each fails closed at its block. ----

    /// Unmasked full-word index `add(B, index)` (agrees across legacy, via-IR and Denote even on wrap).
    function unmaskedWriteAndRead(uint256 index, uint256 key) external returns (uint256 word, bool locked) {
        bytes32 base = QUEUE_BASE;
        assembly ("memory-safe") { tstore(add(base, index), key) }
        assembly ("memory-safe") { word := tload(add(base, index)) }
        locked = _locked;
    }

    /// A narrow index local may carry high bits the legacy pipeline does not clean.
    function badNarrowIndex(uint8 index, uint256 key) external {
        _locked = true;
        bytes32 base = QUEUE_BASE;
        assembly ("memory-safe") { tstore(add(base, index), key) }
    }

    /// A mask of 2^128 or more no longer keeps the slot below 2^256 for every base.
    function badWideMask(uint256 index, uint256 key) external {
        _locked = true;
        bytes32 base = QUEUE_BASE;
        assembly ("memory-safe") { tstore(add(base, and(index, 0xffffffffffffffffffffffffffffffffff)), key) }
    }

    /// A base below 2^128 can be a linear transient slot.
    function badLowBase(uint256 key) external {
        _locked = true;
        bytes32 base = LOW_SLOT;
        assembly ("memory-safe") { tstore(base, key) }
    }

    function badReassignedBase(uint256 key) external {
        _locked = true;
        bytes32 base = QUEUE_BASE;
        base = bytes32(0);
        assembly ("memory-safe") { tstore(base, key) }
    }

    function badArbitraryTload() external returns (uint256 word) {
        _locked = true;
        assembly { word := tload(0) }
    }

    function badTwoStatements(uint256 key) external returns (uint256 out) {
        _locked = true;
        bytes32 base = QUEUE_BASE;
        assembly ("memory-safe") { tstore(base, key)  out := tload(base) }
    }

    function badScratchCall(address target) external returns (bool ok) {
        _locked = true;
        assembly { ok := call(gas(), target, 0, 0, 0, 0, 0) }
    }

    function badDelegatecall(address target, bytes memory payload) external returns (bool ok) {
        _locked = true;
        assembly ("memory-safe") { ok := delegatecall(gas(), target, add(payload, 0x20), mload(payload), 0x00, 0x00) }
    }

    /// A narrow `value` operand may carry dirty high bits on the legacy pipeline.
    function badNarrowValueCall(address target, uint128 value, bytes memory payload)
        external
        returns (bool ok)
    {
        _locked = true;
        assembly ("memory-safe") { ok := call(gas(), target, value, add(payload, 0x20), mload(payload), 0x00, 0x00) }
    }
}
