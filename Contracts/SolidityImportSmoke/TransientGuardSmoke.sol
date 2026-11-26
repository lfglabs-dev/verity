// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Neutral transient-storage smoke fixtures: EIP-1153 `tload` / `tstore` guards.
//
// `TransientGuardAssembly` holds the inline-assembly reentrancy guard shape over a
// precomputed namespaced transient slot constant (ERC-7201-style): the guard reads
// the lock with `tload`, sets it with `tstore`, releases on success and on revert
// the whole transaction (transient slots included) rolls back.
//
// `TransientGuardSlotLib` holds the library-backed UDVT slot guard shape
// (namespaced slot constant wrapped as a `bytes32`-backed UDVT with internal
// `tload`/`tstore` helpers and a custom reentrancy error).
//
// `TransientGuardStateVar` holds the same guard over a `transient bool` state
// variable: no assembly, the importer reads solc's `transientStorageLayout`.
//
// The shapes with inline assembly and the `transient` state-variable shape are
// separate contracts because a root whose closure both reads a `transient` state
// variable and contains inline assembly stays outside this slice.

library GuardTransientSlot {
    type BoolSlot is bytes32;

    function asBool(bytes32 slot) internal pure returns (BoolSlot) {
        return BoolSlot.wrap(slot);
    }

    function tload(BoolSlot slot) internal view returns (bool value) {
        assembly ("memory-safe") {
            value := tload(slot)
        }
    }

    function tstore(BoolSlot slot, bool value) internal {
        assembly ("memory-safe") {
            tstore(slot, value)
        }
    }
}

contract TransientGuardAssembly {
    // Neutral 32-byte namespace slot constant (synthetic fixture value).
    bytes32 private constant _GUARD_TRANSIENT_SLOT =
        0x5f7a1d2e3c4b5a69788796a5b4c3d2e1f00f1e2d3c4b5a69788796a5b4c3d2e1;

    uint256 public count;

    modifier nonReentrant() {
        assembly ("memory-safe") {
            if tload(_GUARD_TRANSIENT_SLOT) { revert(0, 0) }
            tstore(_GUARD_TRANSIENT_SLOT, 1)
        }
        _;
        assembly ("memory-safe") {
            tstore(_GUARD_TRANSIENT_SLOT, 0)
        }
    }

    function bump() external nonReentrant returns (uint256) {
        count += 1;
        return count;
    }

    function bumpEarly(bool early) external nonReentrant returns (uint256) {
        if (early) {
            return count + 10;
        }
        count += 1;
        return count;
    }

    function bumpFail() external nonReentrant {
        count += 1;
        require(false, "guard rollback");
    }

    function guardedEcho(uint256 x) internal nonReentrant returns (uint256) {
        return x * 2;
    }

    function callGuarded(uint256 x) external returns (uint256) {
        return guardedEcho(x);
    }

    function _guardedPair(uint256 x) private returns (bool ok, bytes memory payload) {
        count += 1;
        if (x != 0) {
            ok = true;
            payload = abi.encodePacked(uint32(x), count);
        }
    }

    function forwardGuarded(uint256 x) external nonReentrant returns (bool, bytes memory) {
        return _guardedPair(x);
    }

    function leaveLocked(uint256 v) external {
        assembly ("memory-safe") {
            tstore(_GUARD_TRANSIENT_SLOT, v)
        }
    }

    function lockWord() external view returns (uint256 w) {
        assembly ("memory-safe") {
            w := tload(_GUARD_TRANSIENT_SLOT)
        }
    }

    function callerWord() external view returns (uint256 who) {
        assembly ("memory-safe") {
            who := caller()
        }
    }
}

contract TransientGuardSlotLib {
    using GuardTransientSlot for bytes32;
    using GuardTransientSlot for GuardTransientSlot.BoolSlot;

    error ReentrantCall();

    // Neutral 32-byte namespace slot constant (synthetic fixture value).
    bytes32 private constant _SLOT_LIB_GUARD =
        0x11223344556677889900aabbccddeeff00112233445566778899aabbccddeeff;

    uint256 public count;

    modifier nonReentrant() {
        _enterGuard();
        _;
        _exitGuard();
    }

    function _enterGuard() private {
        if (_isEntered()) {
            revert ReentrantCall();
        }
        _SLOT_LIB_GUARD.asBool().tstore(true);
    }

    function _exitGuard() private {
        _SLOT_LIB_GUARD.asBool().tstore(false);
    }

    function _isEntered() internal view returns (bool) {
        return _SLOT_LIB_GUARD.asBool().tload();
    }

    function bump() external nonReentrant returns (uint256) {
        count += 1;
        return count;
    }

    function bumpEarly(bool early) external nonReentrant returns (uint256) {
        if (early) {
            return count + 10;
        }
        count += 1;
        return count;
    }

    function bumpFail() external nonReentrant {
        count += 1;
        require(false, "slotlib rollback");
    }

    function _slotLibPair(uint256 x) private nonReentrant returns (bool ok, bytes memory payload) {
        count += 1;
        if (x != 0) {
            ok = true;
            payload = abi.encode(count, x);
        }
    }

    function forwardGuarded(uint256 x) external returns (bool ok, bytes memory payload) {
        return _slotLibPair(x);
    }

    function markEntered() external {
        _SLOT_LIB_GUARD.asBool().tstore(true);
    }

    function entered() external view returns (bool) {
        return _isEntered();
    }
}

contract TransientGuardStateVar {
    bool internal transient locked;
    uint256 public count;

    modifier nonReentrant() {
        require(!locked);
        locked = true;
        _;
        locked = false;
    }

    function bump() external nonReentrant returns (uint256) {
        count += 1;
        return count;
    }

    function bumpFail() external nonReentrant {
        count += 1;
        locked = true;
        require(false, "state rollback");
    }

    function _stateVarPair(uint256 x) private returns (bool ok, bytes memory payload) {
        count += 1;
        if (x != 0) {
            ok = true;
            payload = abi.encodePacked(uint16(x), count);
        }
    }

    function forwardGuarded(uint256 x) external nonReentrant returns (bool ok, bytes memory payload) {
        return _stateVarPair(x);
    }

    function markLocked() external {
        locked = true;
    }

    function isLocked() external view returns (bool) {
        return locked;
    }
}
