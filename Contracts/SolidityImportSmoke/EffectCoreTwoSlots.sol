// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `EffectCoreOneSlot.sol` plus one unrelated state variable and one unused function (#2830).
//
// - A discarded `bytes memory` helper call inlines its body whether its result is named or
//   not (formerly a named result was rejected with one state variable).
// - A typed external call without return values to an account without code: legacy encodes
//   the arguments, then checks `extcodesize`; a storage `bytes` argument with a corrupt
//   length reverts with Panic 0x22 before that check (via-IR checks first and is rejected).

interface IByteSink {
    function put(bytes calldata data) external;
    function putWord(uint256 x) external;
}

contract EffectCoreTwoSlots {
    bytes private stored;
    uint256 private unrelated;

    function mark(uint256 x) internal returns (bytes memory r) {
        stored = abi.encodePacked(x);
        r = abi.encodePacked(x, x);
    }

    function markDividing(uint256 x) internal returns (bytes memory r) {
        uint256 q = 10 / x;
        stored = abi.encodePacked(q);
        r = abi.encodePacked(q, q);
    }

    function markEarly(uint256 x) internal returns (bytes memory r) {
        if (x > 5) return abi.encodePacked(x);
        stored = abi.encodePacked(uint8(x));
        r = abi.encodePacked(x, x);
    }

    function markUnassigned(uint256 x) internal returns (bytes memory r) {
        stored = abi.encodePacked(x, uint8(x));
    }

    function markUnnamed(uint256 x) internal returns (bytes memory) {
        stored = abi.encodePacked(uint16(x));
        return "u";
    }

    function discardNamed(uint256 x) external returns (uint256) {
        mark(x);
        return stored.length;
    }

    function discardDividing(uint256 x) external returns (uint256) {
        markDividing(x);
        return stored.length;
    }

    function discardEarly(uint256 x) external returns (uint256) {
        stored = "0123456789";
        markEarly(x);
        return stored.length;
    }

    function discardUnassigned(uint256 x) external returns (uint256) {
        markUnassigned(x);
        return stored.length;
    }

    function discardUnnamed(uint256 x) external returns (uint256) {
        markUnnamed(x);
        return stored.length;
    }

    function voidWord(address target, uint256 x) external {
        uint256 q = 10 / x;
        IByteSink(target).putWord(q);
    }

    function voidStored(address target) external {
        IByteSink(target).put(stored);
    }

    function unusedSetter(uint256 x) external {
        unrelated = x;
    }
}
