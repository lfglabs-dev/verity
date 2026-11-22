// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// A mapping member of a storage struct passed to an internal helper's `mapping(...) storage`
// parameter lowers the same way whatever else the contract declares (#2830): the helper binds
// the mapping's slot, computed once at the call, and indexes it like the member itself. The
// importer counts state variables across the whole compiled source, so each contract of the
// pair is alone in its file; they differ only by one unrelated state variable and one unused
// function.
contract StorageMappingArgumentTwoSlots {
    struct Entry {
        uint256 a;
        uint256 b;
    }

    struct Book {
        uint256 total;
        mapping(address => uint256) bal;
        mapping(uint256 => int256) delta;
        mapping(uint256 => Entry) entries;
        mapping(int8 => uint256) signedKey;
    }

    mapping(uint256 => Book) internal books;
    uint256 internal unrelated;

    function unused() external view returns (uint256) {
        return unrelated;
    }

    function credit(mapping(address => uint256) storage m, address who, uint256 v) internal returns (uint256) {
        m[who] += v;
        return m[who];
    }

    function forward(mapping(address => uint256) storage m, address who, uint256 v) internal returns (uint256) {
        uint256 r = credit(m, who, v);
        return r + 1;
    }

    function clear(mapping(address => uint256) storage m, address who) internal {
        delete m[who];
    }

    function both(mapping(address => uint256) storage m, mapping(address => uint256) storage n, address who)
        internal
        returns (uint256)
    {
        m[who] = 5;
        n[who] += 7;
        return m[who];
    }

    function addDelta(mapping(uint256 => int256) storage m, uint256 k, int256 v) internal returns (int256) {
        m[k] = m[k] + v;
        return m[k];
    }

    function setEntry(mapping(uint256 => Entry) storage m, uint256 k, uint256 v) internal returns (uint256) {
        m[k].a = v;
        m[k].b = v + 1;
        return m[k].a * 1000 + m[k].b;
    }

    function setSigned(mapping(int8 => uint256) storage m, int8 k, uint256 v) internal returns (uint256) {
        m[k] = v;
        return m[k];
    }

    function slotOf(mapping(address => uint256) storage m) internal pure returns (uint256 s) {
        assembly {
            s := m.slot
        }
    }

    function layout() internal pure returns (Book storage b) {
        assembly {
            b.slot := 0x1234
        }
    }

    function deposit(uint256 id, address who, uint256 v) external returns (uint256) {
        books[id].total += v;
        uint256 r = credit(books[id].bal, who, v);
        return r * 1000 + books[id].bal[who] * 10 + books[id].total;
    }

    function forwarded(uint256 id, address who, uint256 v) external returns (uint256) {
        return forward(books[id].bal, who, v);
    }

    function cleared(uint256 id, address who) external returns (uint256) {
        books[id].bal[who] = 9;
        clear(books[id].bal, who);
        return books[id].bal[who];
    }

    // Both parameters denote the same mapping: storage, so each write is seen through the other.
    function aliased(uint256 id, address who) external returns (uint256) {
        uint256 r = both(books[id].bal, books[id].bal, who);
        return r * 100 + books[id].bal[who];
    }

    function shifted(uint256 id, uint256 k, int256 v) external returns (int256) {
        return addDelta(books[id].delta, k, v);
    }

    function entry(uint256 id, uint256 k, uint256 v) external returns (uint256) {
        uint256 r = setEntry(books[id].entries, k, v);
        return r * 10 + books[id].entries[k].b;
    }

    function signedKey(uint256 id, int8 k, uint256 v) external returns (uint256) {
        uint256 r = setSigned(books[id].signedKey, k, v);
        return r * 10 + books[id].signedKey[k];
    }

    function pointer(uint256 id, address who, uint256 v) external returns (uint256) {
        Book storage b = books[id];
        uint256 r = credit(b.bal, who, v);
        return r * 10 + b.bal[who];
    }

    // The key expression is evaluated once, at the call, before the other arguments.
    function keyOrder(uint256 id, address who) external returns (uint256) {
        uint256 i = id;
        uint256 r = credit(books[i].bal, who, i + 1);
        return r * 10 + i;
    }

    function slotOfMember(uint256 id) external returns (uint256) {
        books[id].total = 1;
        return slotOf(books[id].bal);
    }

    function rawSlot(address who, uint256 v) external returns (uint256) {
        Book storage b = layout();
        uint256 r = credit(b.bal, who, v);
        return r * 10 + b.bal[who];
    }

    function rawSlotOf() external returns (uint256) {
        return slotOf(layout().bal);
    }
}
