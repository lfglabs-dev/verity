// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Internal helpers that return a storage struct pointer and then validate it before the
/// caller reads or writes through the returned pointer.
contract StoragePointerGuardFixture {
    struct Item {
        uint256 amount;
        bool active;
    }

    struct Book {
        mapping(uint256 => Item) items;
        uint256 count;
    }

    bytes32 private constant SYNTHETIC_BOOK_SLOT =
        0x1111111111111111111111111111111111111111111111111111111111111100;

    Book internal book;

    error ItemInactive(uint256 id);
    event Touched(uint256 id, uint256 amount);

    /// Raw-slot storage struct helper for a synthetic namespace slot.
    function _rawBook() internal pure returns (Book storage b) {
        assembly {
            b.slot := SYNTHETIC_BOOK_SLOT
        }
    }

    /// A named storage-pointer return assigned first, then guarded by `require`.
    function _activeItem(uint256 id) internal view returns (Item storage item) {
        item = book.items[id];
        require(item.active, ItemInactive(id));
    }

    /// The same shape with an explicit `return` after a reverting branch.
    function _checkedItem(uint256 id) internal view returns (Item storage item) {
        item = book.items[id];
        if (!item.active) {
            revert ItemInactive(id);
        }
        return item;
    }

    /// A multi-statement storage-pointer helper indexing a raw-slot struct pointer.
    function _activeRawItem(uint256 id) internal view returns (Item storage item) {
        Book storage b = _rawBook();
        item = b.items[id];
        require(item.active, ItemInactive(id));
    }

    /// Read and write through the pointer returned by the guarded helper.
    function add(uint256 id, uint256 delta) external returns (uint256) {
        Item storage item = _activeItem(id);
        item.amount += delta;
        emit Touched(id, item.amount);
        return item.amount;
    }

    /// The explicit-return variant.
    function addChecked(uint256 id, uint256 delta) external returns (uint256) {
        Item storage item = _checkedItem(id);
        item.amount += delta;
        return item.amount;
    }

    /// The raw-slot guarded storage-pointer variant.
    function addRaw(uint256 id, uint256 delta) external returns (uint256) {
        Item storage item = _activeRawItem(id);
        item.amount += delta;
        return item.amount;
    }

    /// Seed storage so a caller can reach both the guarded and inactive paths.
    function store(uint256 id, bool active, uint256 amount) external {
        Item storage item = book.items[id];
        item.active = active;
        item.amount = amount;
        book.count += 1;
    }

    /// Seed raw-slot storage so a caller can reach both active and inactive paths.
    function storeRaw(uint256 id, bool active, uint256 amount) external {
        Book storage b = _rawBook();
        Item storage item = b.items[id];
        item.active = active;
        item.amount = amount;
        b.count += 1;
    }

    function read(uint256 id) external view returns (uint256, bool) {
        Item storage item = book.items[id];
        return (item.amount, item.active);
    }

    function readRaw(uint256 id) external view returns (uint256, bool) {
        Book storage b = _rawBook();
        Item storage item = b.items[id];
        return (item.amount, item.active);
    }
}

/// Negative controls for storage-pointer helpers that must remain rejected.
contract StoragePointerGuardRejections {
    struct Item {
        uint256 amount;
        bool active;
    }

    mapping(uint256 => Item) internal items;

    function _afterReturn(uint256 id) internal view returns (Item storage item) {
        item = items[id];
        return item;
        require(item.active);
    }

    function _branchReturn(uint256 id) internal view returns (Item storage item) {
        if (id > 0) {
            return items[id];
        }
        return items[0];
    }

    function readAfterReturn(uint256 id) external view returns (uint256) {
        return _afterReturn(id).amount;
    }

    function readBranchReturn(uint256 id) external view returns (uint256) {
        return _branchReturn(id).amount;
    }
}
