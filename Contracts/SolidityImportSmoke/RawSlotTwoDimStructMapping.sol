// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Synthetic clean-room fixture covering R1:
/// 2D struct-valued mappings inside ERC-7201 raw-slot storage structs
/// (`mapping(uint256 => mapping(uint256 => Entry))` and
/// `mapping(address => mapping(uint256 => Entry))`) with multi-word
/// bit-packed scalar/uint/bool/address/enum fields, direct indexed access,
/// storage-pointer bindings, and exact double-Keccak slot derivation.
contract RawSlotTwoDimStructMapping {
    enum Tier {
        Bronze,
        Silver,
        Gold
    }

    struct Entry {
        uint128 amount;     // word 0, bytes 0..15
        uint64 updatedAt;   // word 0, bytes 16..23
        Tier tier;          // word 0, byte 24
        bool frozen;        // word 0, byte 25
        address owner;      // word 1, bytes 0..19
        uint96 cap;         // word 1, bytes 20..31
    }

    struct Store {
        uint256 nonce;                                      // slot +0
        mapping(uint256 => mapping(uint256 => Entry)) grid; // slot +1
        mapping(address => mapping(uint256 => Entry)) byAccount; // slot +2
    }

    bytes32 private constant STORE_SLOT =
        0x4242424242424242424242424242424242424242424242424242424242424200;

    function _store() private pure returns (Store storage $) {
        assembly ("memory-safe") {
            $.slot := STORE_SLOT
        }
    }

    function _bumpEntry(Entry storage e, uint128 delta, uint64 ts) private {
        e.amount += delta;
        e.updatedAt = ts;
    }

    function _readInnerAmount(
        mapping(uint256 => Entry) storage row,
        uint256 k2
    ) private view returns (uint128) {
        return row[k2].amount;
    }

    function writeDirectGrid(
        uint256 k1,
        uint256 k2,
        uint128 amount,
        uint64 updatedAt,
        uint8 tierRaw,
        bool frozen,
        address owner,
        uint96 cap
    ) external {
        Store storage $ = _store();
        $.nonce += 1;
        $.grid[k1][k2].amount = amount;
        $.grid[k1][k2].updatedAt = updatedAt;
        $.grid[k1][k2].tier = Tier(tierRaw);
        $.grid[k1][k2].frozen = frozen;
        $.grid[k1][k2].owner = owner;
        $.grid[k1][k2].cap = cap;
    }

    function readDirectGrid(uint256 k1, uint256 k2)
        external
        view
        returns (uint128, uint64, uint8, bool, address, uint96)
    {
        Store storage $ = _store();
        return (
            $.grid[k1][k2].amount,
            $.grid[k1][k2].updatedAt,
            uint8($.grid[k1][k2].tier),
            $.grid[k1][k2].frozen,
            $.grid[k1][k2].owner,
            $.grid[k1][k2].cap
        );
    }

    function updateViaPointer(
        uint256 k1,
        uint256 k2,
        uint128 delta,
        uint64 ts,
        bool freeze
    ) external returns (uint128, uint64, bool) {
        Store storage $ = _store();
        Entry storage e = $.grid[k1][k2];
        // Mutate keys after binding to confirm the storage pointer slot was frozen.
        k1 += 77;
        k2 += 88;
        _bumpEntry(e, delta, ts);
        e.frozen = freeze;
        return (e.amount, e.updatedAt, e.frozen);
    }

    function writeAndReadAccount(
        address acct,
        uint256 bucket,
        uint128 amount,
        uint8 tierRaw,
        address owner,
        uint96 cap
    ) external returns (uint128, uint8, address, uint96) {
        Store storage $ = _store();
        $.byAccount[acct][bucket] = Entry({
            amount: amount,
            updatedAt: 42,
            tier: Tier(tierRaw),
            frozen: true,
            owner: owner,
            cap: cap
        });
        Entry memory copy = $.byAccount[acct][bucket];
        return (copy.amount, uint8(copy.tier), copy.owner, copy.cap);
    }

    function readRowHelper(uint256 k1, uint256 k2) external view returns (uint128) {
        Store storage $ = _store();
        return _readInnerAmount($.grid[k1], k2);
    }

    function deleteGridEntry(uint256 k1, uint256 k2) external {
        Store storage $ = _store();
        delete $.grid[k1][k2];
    }

    function rawGridWords(uint256 k1, uint256 k2)
        external
        view
        returns (bytes32 w0, bytes32 w1)
    {
        uint256 gridSlot = uint256(STORE_SLOT) + 1;
        bytes32 outerSlot = keccak256(abi.encode(k1, gridSlot));
        bytes32 entrySlot = keccak256(abi.encode(k2, outerSlot));
        assembly ("memory-safe") {
            w0 := sload(entrySlot)
            w1 := sload(add(entrySlot, 1))
        }
    }

    function rawAccountWords(address acct, uint256 bucket)
        external
        view
        returns (bytes32 w0, bytes32 w1)
    {
        uint256 acctSlot = uint256(STORE_SLOT) + 2;
        bytes32 outerSlot = keccak256(abi.encode(acct, acctSlot));
        bytes32 entrySlot = keccak256(abi.encode(bucket, outerSlot));
        assembly ("memory-safe") {
            w0 := sload(entrySlot)
            w1 := sload(add(entrySlot, 1))
        }
    }
}
