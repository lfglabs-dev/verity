// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Transient state variables in closures whose inline assembly does not touch transient
/// storage: a namespaced storage getter (`$.slot := LOCATION`) and full-word Yul locals.
/// A transient flag switches a counter update to a deferred queue that a later call of the
/// same transaction drains.
contract TransientNeutralAssemblySequence {
    struct Main {
        uint256 total;
        uint256 checked;
    }

    // keccak256(abi.encode(uint256(keccak256("verity.fixture.namespaced")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant MAIN_LOCATION =
        0x9ee206bc124160cd40c828f4614e7d92dc2e9850e42b9bc6bcad127f50b4a500;

    bool private transient deferred;
    uint256 private transient queued;
    uint8 private transient small;

    modifier fullWordModifier() {
        uint256 word;
        assembly { word := 1 }
        _;
    }

    modifier narrowModifier() {
        uint8 word;
        assembly { word := 1 }
        _;
    }

    function _main() private pure returns (Main storage $) {
        assembly { $.slot := MAIN_LOCATION }
    }

    function enter() external {
        deferred = true;
    }

    function act(uint256 amount) external returns (uint256) {
        Main storage $ = _main();
        $.total += amount;
        if (deferred) {
            queued += 1;
        } else {
            $.checked += 1;
        }
        return queued;
    }

    function close() external returns (uint256 drained) {
        Main storage $ = _main();
        deferred = false;
        drained = queued;
        queued = 0;
        $.checked += drained;
    }

    function state() external view returns (bool, uint256, uint256, uint256) {
        Main storage $ = _main();
        return (deferred, queued, $.total, $.checked);
    }

    function fullWordLocal(uint256 x) external returns (uint256 y) {
        uint256 t;
        assembly { t := add(x, 1) }
        queued = t;
        small = uint8(t);
        y = queued + small;
    }

    function signedAndBytes(int256 a, bytes32 b) external returns (uint256) {
        int256 s;
        bytes32 w;
        assembly {
            s := sub(0, a)
            w := not(b)
        }
        queued = uint256(s) ^ uint256(w);
        return queued;
    }

    function inModifier() external fullWordModifier returns (bool) {
        return deferred;
    }

    function namespacedSlotRead() external view returns (uint256 s, bool d) {
        Main storage $ = _main();
        d = deferred;
        assembly { s := sload($.slot) }
    }

    // Shapes that stay rejected in a transient closure.

    function narrowLocal(uint256 x) external {
        bool b;
        assembly { b := x }
        deferred = b;
    }

    function narrowParameter(uint8 v) external returns (uint256 word) {
        small = v;
        assembly { word := v }
    }

    function narrowInModifier() external narrowModifier returns (bool) {
        return deferred;
    }

    function transientSlot() external view returns (uint256 s) {
        assembly { s := queued.slot }
    }

    function computedTransientSlot(uint256 key) external {
        uint256 n = queued;
        bytes32 base = MAIN_LOCATION;
        assembly { tstore(add(base, n), key) }
        queued = n + 1;
    }

    function callInAssembly(address target) external returns (uint256 ok) {
        deferred = true;
        assembly { ok := call(gas(), target, 0, 0, 0, 0, 0) }
    }
}
