// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type ShortString is bytes32;
type Delay is uint112;

library StorageSlot {
    struct AddressSlot {
        address value;
    }

    struct BooleanSlot {
        bool value;
    }

    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    struct Int256Slot {
        int256 value;
    }

    struct StringSlot {
        string value;
    }

    struct BytesSlot {
        bytes value;
    }

    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getBooleanSlot(bytes32 slot) internal pure returns (BooleanSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getInt256Slot(bytes32 slot) internal pure returns (Int256Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getStringSlot(string storage store) internal pure returns (StringSlot storage r) {
        assembly ("memory-safe") {
            r.slot := store.slot
        }
    }

    function getBytesSlot(bytes storage store) internal pure returns (BytesSlot storage r) {
        assembly ("memory-safe") {
            r.slot := store.slot
        }
    }
}

library ShortStrings {
    bytes32 private constant FALLBACK_SENTINEL = 0x00000000000000000000000000000000000000000000000000000000000000FF;

    error InvalidShortString();
    error StringTooLong(uint256 length);

    function toShortString(string memory str) internal pure returns (ShortString) {
        bytes memory bstr = bytes(str);
        uint256 bLen = bstr.length;
        if (bLen > 31) {
            revert StringTooLong(bLen);
        }
        return ShortString.wrap(bytes32(uint256(bytes32(bstr)) | bLen));
    }

    function toString(ShortString sstr) internal pure returns (string memory) {
        uint256 len = byteLength(sstr);
        string memory str = new string(32);
        assembly ("memory-safe") {
            mstore(str, len)
            mstore(add(str, 0x20), sstr)
        }
        return str;
    }

    function byteLength(ShortString sstr) internal pure returns (uint256) {
        uint256 result = uint256(ShortString.unwrap(sstr)) & 0xFF;
        if (result > 31) {
            revert InvalidShortString();
        }
        return result;
    }

    function toShortStringWithFallback(string memory value, string storage store) internal returns (ShortString) {
        if (bytes(value).length < 32) {
            return toShortString(value);
        } else {
            StorageSlot.getStringSlot(store).value = value;
            return ShortString.wrap(FALLBACK_SENTINEL);
        }
    }

    function toStringWithFallback(ShortString value, string storage store) internal view returns (string memory) {
        if (ShortString.unwrap(value) != FALLBACK_SENTINEL) {
            return toString(value);
        } else {
            return store;
        }
    }

    function byteLengthWithFallback(ShortString value, string storage store) internal view returns (uint256) {
        if (ShortString.unwrap(value) != FALLBACK_SENTINEL) {
            return byteLength(value);
        } else {
            return bytes(store).length;
        }
    }
}

library Time {
    function timestamp() internal view returns (uint48) {
        return uint48(block.timestamp);
    }

    function blockNumber() internal view returns (uint48) {
        return uint48(block.number);
    }

    function toDelay(uint32 duration) internal pure returns (Delay) {
        return Delay.wrap(uint112(duration) << 32);
    }

    function _getFullAt(
        Delay self,
        uint48 timepoint
    ) private pure returns (uint32 valueBefore, uint32 valueAfter, uint48 effect) {
        (valueBefore, valueAfter, effect) = unpack(self);
        if (effect <= timepoint) {
            valueBefore = valueAfter;
            effect = 0;
        }
        return (valueBefore, valueAfter, effect);
    }

    function getFull(Delay self) internal view returns (uint32 valueBefore, uint32 valueAfter, uint48 effect) {
        return _getFullAt(self, timestamp());
    }

    function get(Delay self) internal view returns (uint32) {
        (uint32 delay, , ) = getFull(self);
        return delay;
    }

    function withUpdate(
        Delay self,
        uint32 newValue,
        uint32 minSetback
    ) internal view returns (Delay updatedDelay, uint48 effect) {
        uint32 value = get(self);
        uint32 setback = value > newValue ? value - newValue : 0;
        if (minSetback > setback) {
            setback = minSetback;
        }
        effect = timestamp() + setback;
        return (pack(value, newValue, effect), effect);
    }

    function unpack(Delay self) internal pure returns (uint32 valueBefore, uint32 valueAfter, uint48 effect) {
        uint112 raw = Delay.unwrap(self);
        valueBefore = uint32(raw);
        valueAfter = uint32(raw >> 32);
        effect = uint48(raw >> 64);
        return (valueBefore, valueAfter, effect);
    }

    function pack(uint32 valueBefore, uint32 valueAfter, uint48 effect) internal pure returns (Delay) {
        return Delay.wrap((uint112(effect) << 64) | (uint112(valueAfter) << 32) | uint112(valueBefore));
    }
}

contract SequenceFixture {
    using ShortStrings for *;
    using Time for *;

    error VaultStepBlocked(uint256 input, bytes32 digest, uint256 activeDelay);
    event VaultStepObserved(uint256 indexed totalScore, bytes32 digest, uint256 activeDelay);

    bytes32 private constant ADDR_SLOT = keccak256("verity.smoke.storage_slot.address");
    bytes32 private constant BOOL_SLOT = keccak256("verity.smoke.storage_slot.boolean");
    bytes32 private constant BYTES32_SLOT = keccak256("verity.smoke.storage_slot.bytes32");
    bytes32 private constant UINT256_SLOT = keccak256("verity.smoke.storage_slot.uint256");
    bytes32 private constant INT256_SLOT = keccak256("verity.smoke.storage_slot.int256");

    // keccak256(abi.encode(uint256(keccak256("verity.storage.VaultStorage")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant VAULT_STORAGE_LOCATION =
        0x79b4402849e9301de01c1662e83cb9dc5a09a5206b5ed4de7429ce4e16d79900;

    struct VaultStorage {
        address admin;
        uint48 unlockAt;
        uint32 epoch;
        bool paused;
        uint256 totalAssets;
        int256 netDelta;
        bytes32 configHash;
        Delay withdrawalDelay;
        ShortString shortName;
        mapping(address => uint256) balances;
        mapping(bytes32 => uint256) allowances;
    }

    string private _nameFallback;
    bytes private _bytesFallback;
    uint256 private totalScore;
    bytes32 private lastDigest;

    function _getVaultStorage() private pure returns (VaultStorage storage $) {
        assembly ("memory-safe") {
            $.slot := VAULT_STORAGE_LOCATION
        }
    }

    function _creditAccount(VaultStorage storage $, address account, uint256 amount) private returns (uint256) {
        $.balances[account] += amount;
        $.totalAssets += amount;
        return $.balances[account];
    }

    function _recordBytesFallback(bytes memory payload) private returns (uint256) {
        StorageSlot.getBytesSlot(_bytesFallback).value = payload;
        return StorageSlot.getBytesSlot(_bytesFallback).value.length;
    }

    function change(uint256 input) external returns (uint256) {
        VaultStorage storage $ = _getVaultStorage();
        uint256 branch = input % 6;
        bytes32 tag = bytes32(uint256(0x9000) + (input & 0x7));

        if (branch == 0) {
            $.admin = msg.sender;
            $.unlockAt = Time.timestamp() + 12;
            uint32 ep = ++$.epoch;
            $.paused = (ep & 1) == 1;
            $.netDelta += int256(uint256(input & 0xffff));
            $.configHash ^= bytes32(input);
            $.withdrawalDelay = Time.toDelay(uint32(10 + (input & 0xf)));
            $.shortName = string("ParetoVault").toShortStringWithFallback(_nameFallback);
            StorageSlot.getAddressSlot(ADDR_SLOT).value = msg.sender;
            StorageSlot.getBooleanSlot(BOOL_SLOT).value = true;
            StorageSlot.getUint256Slot(UINT256_SLOT).value = (input & 0xffff) + 1;
            StorageSlot.getInt256Slot(INT256_SLOT).value = -int256(uint256((input & 0xff) + 1));
            StorageSlot.getBytes32Slot(BYTES32_SLOT).value = tag;
            _creditAccount($, msg.sender, (input & 0xff) + 10);
            $.allowances[tag] += (input & 0x3f) + 5;
        } else if (branch == 1) {
            (Delay updated, uint48 eff) = $.withdrawalDelay.withUpdate(uint32(4 + (input & 0x7)), uint32(3));
            $.withdrawalDelay = updated;
            $.unlockAt = eff;
            $.shortName = string("Pareto-Credit-Vault-Long-Name-With-Fallback-Slot").toShortStringWithFallback(_nameFallback);
            StorageSlot.Uint256Slot storage uSlot = StorageSlot.getUint256Slot(UINT256_SLOT);
            uSlot.value += 7;
            ++uSlot.value;
            StorageSlot.Int256Slot storage iSlot = StorageSlot.getInt256Slot(INT256_SLOT);
            iSlot.value += 3;
            --iSlot.value;
            StorageSlot.getBytes32Slot(BYTES32_SLOT).value ^= bytes32(uint256(0x55aa));
            _recordBytesFallback(hex"112233445566");
        } else if (branch == 2) {
            string memory recovered = $.shortName.toStringWithFallback(_nameFallback);
            uint256 recLen = $.shortName.byteLengthWithFallback(_nameFallback);
            require(bytes(recovered).length == recLen, "short string length mismatch");
            delete $.paused;
            if ($.balances[msg.sender] >= 3) {
                $.balances[msg.sender] -= 3;
                $.totalAssets -= 3;
            }
            ++$.allowances[tag];
        } else if (branch == 3) {
            ShortString s = ShortStrings.toShortString("AlphaTranche");
            string memory str = ShortStrings.toString(s);
            uint256 blen = ShortStrings.byteLength(s);
            require(bytes(str).length == blen && blen == 12, "roundtrip short string mismatch");
            $.shortName = s;
            _recordBytesFallback(bytes(str));
        } else if (branch == 4) {
            delete StorageSlot.getBooleanSlot(BOOL_SLOT).value;
            delete StorageSlot.getUint256Slot(UINT256_SLOT).value;
            delete $.unlockAt;
            delete $.allowances[tag];
            delete StorageSlot.getBytesSlot(_bytesFallback).value;
        } else {
            (uint32 vb, uint32 va, uint48 eff) = $.withdrawalDelay.getFull();
            uint32 curDelay = $.withdrawalDelay.get();
            $.epoch += uint32((vb + va + curDelay) & 0xff);
            $.unlockAt = eff + Time.blockNumber();
        }

        uint256 activeDelay = uint256($.withdrawalDelay.get());
        uint256 nameLen = $.shortName.byteLengthWithFallback(_nameFallback);
        uint256 uSlotVal = StorageSlot.getUint256Slot(UINT256_SLOT).value;
        uint256 balVal = $.balances[msg.sender];
        uint256 allowVal = $.allowances[tag];
        uint256 bytesFallbackLen = StorageSlot.getBytesSlot(_bytesFallback).value.length;
        address curAdmin = $.admin;
        uint48 curUnlock = $.unlockAt;
        uint32 curEpoch = $.epoch;
        uint256 curSummary = $.totalAssets + uSlotVal + balVal + allowVal + nameLen + bytesFallbackLen + ($.paused ? 1 : 0);
        bytes32 digest = keccak256(
            abi.encodePacked(
                curAdmin,
                curUnlock,
                curEpoch,
                curSummary
            )
        );

        if (input == 21) {
            revert VaultStepBlocked(input, digest, activeDelay);
        }

        uint256 metric = (uint256(digest) & 0xffffffff) + activeDelay + curSummary;
        totalScore += metric;
        lastDigest = digest;
        emit VaultStepObserved(totalScore, digest, activeDelay);
        require(input != 20, "storage slot rollback");
        return totalScore;
    }

    function slotAndShortStringStep(
        string memory label,
        uint32 targetDelay,
        uint32 minSetback,
        uint256 mode
    ) external returns (string memory) {
        VaultStorage storage $ = _getVaultStorage();
        if (mode == 99) {
            // InvalidShortString path: low byte 32 > 31
            return ShortStrings.toString(ShortString.wrap(bytes32(uint256(32))));
        }
        if (mode % 2 == 0) {
            ShortString direct = label.toShortString();
            $.shortName = direct;
        } else {
            $.shortName = label.toShortStringWithFallback(_nameFallback);
        }
        (Delay nextDelay, uint48 eff) = $.withdrawalDelay.withUpdate(targetDelay, minSetback);
        $.withdrawalDelay = nextDelay;
        $.unlockAt = eff;
        uint256 len = $.shortName.byteLengthWithFallback(_nameFallback);
        StorageSlot.getUint256Slot(UINT256_SLOT).value += len + uint256(targetDelay);
        bytes32 rawShort = ShortString.unwrap($.shortName);
        uint112 rawDelay = Delay.unwrap(nextDelay);
        bytes32 d = keccak256(abi.encodePacked(rawShort, rawDelay, eff, len));
        lastDigest = d;
        totalScore += (uint256(d) & 0xffffffff) + len + uint256($.withdrawalDelay.get());
        return $.shortName.toStringWithFallback(_nameFallback);
    }

    function vaultLabel() external view returns (string memory) {
        VaultStorage storage $ = _getVaultStorage();
        return $.shortName.toStringWithFallback(_nameFallback);
    }

    function fail() external {
        VaultStorage storage $ = _getVaultStorage();
        $.totalAssets += 777;
        StorageSlot.getUint256Slot(UINT256_SLOT).value += 555;
        bytes32 curDigest = lastDigest;
        uint256 curDelay = uint256($.withdrawalDelay.get());
        revert VaultStepBlocked(999, curDigest, curDelay);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        VaultStorage storage $ = _getVaultStorage();
        uint256 summary =
            $.totalAssets +
            uint256($.epoch) +
            uint256($.unlockAt) +
            uint256($.withdrawalDelay.get()) +
            $.shortName.byteLengthWithFallback(_nameFallback) +
            StorageSlot.getUint256Slot(UINT256_SLOT).value +
            (StorageSlot.getBooleanSlot(BOOL_SLOT).value ? 100 : 0) +
            ($.paused ? 50 : 0);
        return (totalScore, lastDigest, summary);
    }
}
