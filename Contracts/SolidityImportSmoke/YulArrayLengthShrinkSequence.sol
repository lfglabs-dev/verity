// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

// Inline-assembly dynamic memory-array length shrink (`assembly { mstore(x, n) }`, Refs #2620):
// sentinel-linked-list pagination (shrink-to-0, shrink-to-partial, no-shrink, post-shrink
// allocation), lone and tuple dynamic array ABI returns after shrink, post-shrink `.length`,
// in-bounds and out-of-bounds (`Panic(0x32)`) element indexing over retained trailing words,
// post-shrink aliasing and helper reads, `for`-loop filtered compaction, straight-line array
// helper shrink via checked subtraction, and narrow `uint16[]` sequential shrinks.
contract YulArrayLengthShrinkFixture {
    address internal constant SENTINEL = address(0x1);
    uint256 internal constant CONST_KEEP = 1 + 2;

    mapping(address => address) private nextItem;
    uint256 private digest;

    function initList() external {
        require(nextItem[SENTINEL] == address(0), "already initialized");
        nextItem[SENTINEL] = SENTINEL;
        digest = digest ^ 0x11;
    }

    function addItem(address item) external {
        require(item != address(0) && item != SENTINEL, "invalid item");
        require(nextItem[item] == address(0), "duplicate item");
        if (nextItem[SENTINEL] == address(0)) {
            nextItem[SENTINEL] = SENTINEL;
        }
        nextItem[item] = nextItem[SENTINEL];
        nextItem[SENTINEL] = item;
        digest = digest + uint256(uint160(item)) + 1;
    }

    function fail() external {
        digest = digest + 99;
        revert("fail");
    }

    function readState() external view returns (uint256) {
        return digest;
    }

    function paginate(address start, uint256 pageSize)
        external
        view
        returns (address[] memory page, address next)
    {
        require(pageSize <= 8, "page cap");
        page = new address[](pageSize);
        uint256 count = 0;
        next = nextItem[start];
        while (next != address(0) && next != SENTINEL && count < pageSize) {
            page[count] = next;
            next = nextItem[next];
            count++;
        }
        if (next != SENTINEL && count > 0) {
            next = page[count - 1];
        }
        // Shrink allocated page header in place to actual count.
        assembly {
            mstore(page, count)
        }
    }

    function paginateThenAllocate(address start, uint256 pageSize, uint256 tag)
        external
        view
        returns (address[] memory page, address next, uint256 scratchSum)
    {
        require(pageSize <= 8, "page cap");
        page = new address[](pageSize);
        uint256 count = 0;
        address cur = nextItem[start];
        while (cur != address(0) && cur != SENTINEL && count < pageSize) {
            page[count] = cur;
            cur = nextItem[cur];
            count++;
        }
        next = cur;
        assembly ("memory-safe") {
            mstore(page, count)
        }
        uint256[] memory scratch = new uint256[](2);
        scratch[0] = tag ^ page.length;
        scratch[1] = count + 7;
        scratchSum = scratch[0] + scratch[1];
    }

    function returnedShrunkArray(uint256 cap, uint256 keep, uint256 seed)
        external
        pure
        returns (uint256[] memory)
    {
        require(cap <= 8 && keep <= cap, "bounds");
        uint256[] memory xs = new uint256[](cap);
        for (uint256 i = 0; i < cap; i++) {
            xs[i] = seed + i + 100;
        }
        assembly ("memory-safe") {
            mstore(xs, keep)
        }
        return xs;
    }

    function _sumArray(uint256[] memory arr) internal pure returns (uint256 acc) {
        for (uint256 i = 0; i < arr.length; i++) {
            acc = acc + arr[i];
        }
    }

    function inspectPostShrink(uint256 cap, uint256 keep, uint256 probeIdx)
        external
        returns (uint256 lenAfter, uint256 probed, uint256 aliasLen, bytes32 encodedHash)
    {
        require(cap <= 8 && keep <= cap, "bounds");
        uint256[] memory xs = new uint256[](cap);
        for (uint256 i = 0; i < cap; i++) {
            xs[i] = 0x1000 + i;
        }
        assembly {
            mstore(xs, keep)
        }
        lenAfter = xs.length;
        uint256[] memory aliasView;
        aliasView = xs;
        aliasLen = aliasView.length;
        uint256 sumVal = _sumArray(aliasView);
        encodedHash = keccak256(abi.encode(xs, sumVal));
        digest = (digest ^ lenAfter) + (uint256(encodedHash) % 100000);
        if (probeIdx != type(uint256).max) {
            probed = xs[probeIdx];
        }
    }

    function filterCompact(uint256 a, uint256 b, uint256 c, uint256 d)
        external
        pure
        returns (bytes32[] memory out)
    {
        out = new bytes32[](4);
        uint256[] memory raw = new uint256[](4);
        raw[0] = a;
        raw[1] = b;
        raw[2] = c;
        raw[3] = d;
        uint256 kept = 0;
        for (uint256 i = 0; i < 4; i++) {
            if (raw[i] != 0) {
                out[kept] = bytes32(raw[i]);
                kept++;
            }
        }
        assembly {
            mstore(out, kept)
        }
    }

    function _buildFixed3Shrunk(uint256 drop, uint256 base)
        internal
        pure
        returns (uint256[] memory)
    {
        require(drop <= 3, "drop");
        uint256 keep = 3 - drop;
        uint256[] memory arr = new uint256[](3);
        arr[0] = base + 10;
        arr[1] = base + 20;
        arr[2] = base + 30;
        assembly {
            mstore(arr, keep)
        }
        return arr;
    }

    function helperShrinkSub(uint256 drop, uint256 base)
        external
        pure
        returns (uint256[] memory)
    {
        return _buildFixed3Shrunk(drop, base);
    }

    function _leafShrinkConst(uint256 base) internal pure returns (uint256[] memory) {
        uint256[] memory arr = new uint256[](5);
        arr[0] = base + 1;
        arr[1] = base + 2;
        arr[2] = base + 3;
        arr[3] = base + 4;
        arr[4] = base + 5;
        assembly {
            mstore(arr, CONST_KEEP)
        }
        return arr;
    }

    function _midShadowConst(uint256 CONST_KEEP, uint256 extra)
        internal
        pure
        returns (uint256[] memory)
    {
        return _leafShrinkConst(extra + CONST_KEEP);
    }

    function helperConstShadow(uint256 CONST_KEEP, uint256 base)
        external
        pure
        returns (uint256[] memory)
    {
        return _midShadowConst(1, base + CONST_KEEP);
    }

    function shrinkNarrowAndZero(uint256 cap, uint256 mid, bool clearAll)
        external
        pure
        returns (uint16[] memory)
    {
        require(cap <= 6 && mid <= cap, "bounds");
        uint16[] memory arr = new uint16[](cap);
        for (uint256 i = 0; i < cap; i++) {
            arr[i] = uint16(0x0200 + i);
        }
        assembly {
            mstore(arr, mid)
        }
        if (clearAll) {
            assembly {
                mstore(arr, 0)
            }
        }
        return arr;
    }
}
