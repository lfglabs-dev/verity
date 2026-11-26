// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Packed 32-bit lane memory cursor `while (ScanIterLib.hasMore(iter))` fixture.
interface IItemOracle {
    function score(uint256 item) external view returns (uint256);
}

struct ScanIter {
    uint256 word;
    uint256 idx;
    uint256 end;
}

library ScanIterLib {
    function makeScanIter(uint256[64] storage arr, uint256 count) internal view returns (ScanIter memory c) {
        c.idx = 0;
        c.end = count;
        if (count > 0) {
            c.word = arr[0];
        }
    }

    function hasMore(ScanIter memory c) internal pure returns (bool) {
        return c.idx < c.end;
    }

    function next(uint256[64] storage arr, ScanIter memory c) internal view returns (uint32) {
        require(c.idx < c.end);
        uint32 v = uint32(c.word & 0xffffffff);
        unchecked {
            ++c.idx;
        }
        if (c.idx % 8 == 0) {
            if (c.idx < c.end) {
                c.word = arr[c.idx / 8];
            }
        } else {
            c.word >>= 32;
        }
        return v;
    }
}

library ReaderLib {
    function readItem(
        uint256 groupId,
        uint32 itemId,
        address account
    ) internal pure returns (uint256 val, bool ok) {
        uint256 accountTag = uint256(uint160(account)) & 0xff;
        val = (uint256(itemId) + groupId) * 3 + accountTag;
        ok = (itemId < 100);
    }

    function combine(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }
}

contract CursorWhileFixture {
    using ScanIterLib for ScanIter;

    struct Bucket {
        uint256 count;
        uint256[64] words;
    }

    uint256 internal itemCount;
    uint256[64] internal packedSlots;
    Bucket internal bucket;

    function pushItem(uint32 v) external {
        uint256 idx = itemCount;
        require(idx < 512);
        uint256 slotIdx = idx / 8;
        uint256 shift = (idx % 8) * 32;
        uint256 mask = ~(uint256(0xffffffff) << shift);
        packedSlots[slotIdx] = (packedSlots[slotIdx] & mask) | (uint256(v) << shift);
        unchecked {
            itemCount = idx + 1;
        }
    }

    function pushBucketItem(uint32 v) external {
        uint256 idx = bucket.count;
        require(idx < 512);
        uint256 slotIdx = idx / 8;
        uint256 shift = (idx % 8) * 32;
        uint256 mask = ~(uint256(0xffffffff) << shift);
        bucket.words[slotIdx] = (bucket.words[slotIdx] & mask) | (uint256(v) << shift);
        unchecked {
            bucket.count = idx + 1;
        }
    }

    function resetItems() external {
        itemCount = 0;
        bucket.count = 0;
    }

    function _sumLocal(uint256[64] storage arr, uint256 count) internal view returns (uint256 total) {
        ScanIter memory iter = ScanIterLib.makeScanIter(arr, count);
        while (ScanIterLib.hasMore(iter)) {
            uint32 item = ScanIterLib.next(arr, iter);
            total += uint256(item);
        }
    }

    function sumPackedLocal() external view returns (uint256) {
        return _sumLocal(packedSlots, itemCount);
    }

    function sumPackedUsingFor() external view returns (uint256 total, uint256 seen) {
        ScanIter memory iter = ScanIterLib.makeScanIter(packedSlots, itemCount);
        while (iter.hasMore()) {
            uint32 item = ScanIterLib.next(packedSlots, iter);
            total += uint256(item) * (seen + 1);
            unchecked {
                ++seen;
            }
        }
    }

    function sumBucketLocal() external view returns (uint256) {
        return _sumLocal(bucket.words, bucket.count);
    }

    function _scanWithOracle(uint256[64] storage arr, uint256 count, address oracle)
        internal
        view
        returns (uint256 total, bool allOdd)
    {
        allOdd = true;
        ScanIter memory iter = ScanIterLib.makeScanIter(arr, count);
        while (ScanIterLib.hasMore(iter)) {
            uint32 item = ScanIterLib.next(arr, iter);
            uint256 val = IItemOracle(oracle).score(uint256(item));
            if ((val & 1) == 0) {
                allOdd = false;
            }
            total += val;
        }
    }

    function scanPackedWithOracle(address oracle) external view returns (uint256 total, bool allOdd) {
        return _scanWithOracle(packedSlots, itemCount, oracle);
    }

    function _scanNestedNamedArgs(uint256[64] storage arr, uint256 count, uint256 gid, address user)
        internal
        view
        returns (uint256 total, bool allOk)
    {
        allOk = true;
        ScanIter memory iter = ScanIterLib.makeScanIter(arr, count);
        while (ScanIterLib.hasMore(iter)) {
            (uint256 val, bool ok) = ReaderLib.readItem({
                groupId: gid,
                itemId: ScanIterLib.next(arr, iter),
                account: user
            });
            total += val;
            if (!ok) {
                allOk = false;
            }
        }
    }

    function scanNestedNamedArgs(uint256 gid, address user)
        external
        view
        returns (uint256 total, bool allOk)
    {
        return _scanNestedNamedArgs(packedSlots, itemCount, gid, user);
    }

    function scanNestedOracleCall(address oracle)
        external
        view
        returns (uint256 total, bool allOdd)
    {
        allOdd = true;
        ScanIter memory iter = ScanIterLib.makeScanIter(packedSlots, itemCount);
        while (ScanIterLib.hasMore(iter)) {
            uint256 val = IItemOracle(oracle).score(uint256(ScanIterLib.next(packedSlots, iter)));
            if ((val & 1) == 0) {
                allOdd = false;
            }
            total += val;
        }
    }

    // Negative control 1: cursor step inside short-circuiting RHS of `&&` is NOT unconditional.
    function badShortCircuitStep(bool flag) external view returns (uint256 hits) {
        ScanIter memory iter = ScanIterLib.makeScanIter(packedSlots, itemCount);
        while (ScanIterLib.hasMore(iter)) {
            bool b = flag && (ScanIterLib.next(packedSlots, iter) > 0);
            if (b) {
                unchecked {
                    ++hits;
                }
            }
        }
    }

    // Negative control 2: sibling argument reads `iter.idx` alongside nested `ScanIterLib.next(arr, iter)`.
    function badSiblingCursorRead() external view returns (uint256 total) {
        ScanIter memory iter = ScanIterLib.makeScanIter(packedSlots, itemCount);
        while (ScanIterLib.hasMore(iter)) {
            uint256 val = ReaderLib.combine(iter.idx, uint256(ScanIterLib.next(packedSlots, iter)));
            total += val;
        }
    }

    // Negative control 3: two cursor steps in a single statement.
    function badDoubleStep() external view returns (uint256 total) {
        ScanIter memory iter = ScanIterLib.makeScanIter(packedSlots, itemCount);
        while (ScanIterLib.hasMore(iter)) {
            uint256 val = ReaderLib.combine(
                uint256(ScanIterLib.next(packedSlots, iter)),
                uint256(ScanIterLib.next(packedSlots, iter))
            );
            total += val;
        }
    }
}
