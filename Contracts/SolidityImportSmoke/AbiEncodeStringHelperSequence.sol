// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type PackedString is bytes32;

// A string packed into one word (data left-aligned, length in the low byte), with a
// sentinel that selects a storage fallback. Decoding reverts with a custom error on a
// length byte above 31.
library PackedStrings {
    bytes32 internal constant FALLBACK_SENTINEL =
        0x00000000000000000000000000000000000000000000000000000000000000FF;

    error InvalidPackedString(uint256 raw);

    function byteLength(PackedString value) internal pure returns (uint256) {
        uint256 raw = uint256(PackedString.unwrap(value));
        uint256 result = raw & 0xFF;
        if (result > 0x1f) {
            revert InvalidPackedString(raw);
        }
        return result;
    }

    function toString(PackedString value) internal pure returns (string memory) {
        uint256 len = byteLength(value);
        string memory str = new string(0x20);
        assembly ("memory-safe") {
            mstore(str, len)
            mstore(add(str, 0x20), value)
        }
        return str;
    }

    function toStringWithFallback(PackedString value, string storage store)
        internal
        pure
        returns (string memory)
    {
        if (PackedString.unwrap(value) != FALLBACK_SENTINEL) {
            return toString(value);
        } else {
            return store;
        }
    }
}

// View helpers returning `string` / `bytes` (possibly reverting with a custom error) as
// `abi.encode` arguments and as components of a root return tuple. Both solc pipelines
// evaluate the arguments left to right, so of two failing arguments the first one's
// revert data is returned.
contract SequenceFixture {
    using PackedStrings for PackedString;

    bytes32 internal constant DOMAIN_TYPEHASH =
        keccak256("Domain(string name,string version,uint256 chainId,address verifyingContract)");

    PackedString internal packedName;
    PackedString internal packedVersion;
    string internal nameFallback;
    string internal versionFallback;
    bytes internal tag;
    uint256 internal saved;

    function _name() internal view returns (string memory) {
        return packedName.toStringWithFallback(nameFallback);
    }

    function _version() internal view returns (string memory) {
        return packedVersion.toStringWithFallback(versionFallback);
    }

    function _tag(uint256 k) internal view returns (bytes memory) {
        if (k % 3 == 0) {
            return tag;
        }
        return abi.encodePacked(uint16(k), tag);
    }

    // Empty, 3-byte and 31-byte packed strings; 32-byte, 33-byte and empty storage
    // fallbacks; an invalid length byte (decoding reverts with `raw` in the revert data).
    function _pack(uint256 raw) internal returns (PackedString) {
        uint256 k = raw % 7;
        if (k == 0) {
            return PackedString.wrap(bytes32(0));
        } else if (k == 1) {
            return PackedString.wrap(0x6162630000000000000000000000000000000000000000000000000000000003);
        } else if (k == 2) {
            return PackedString.wrap(0x7468697274792d6f6e652d627974652d646f6d61696e2d6e616d652d78797a1f);
        } else if (k == 3) {
            nameFallback = "thirty-two-byte-domain-name-wxyz";
            versionFallback = "thirty-two-byte-domain-name-wxyz";
        } else if (k == 4) {
            nameFallback = "thirty-three-byte-domain-name-xyz";
            versionFallback = "thirty-three-byte-domain-name-xyz";
        } else if (k == 5) {
            nameFallback = "";
            versionFallback = "";
        } else {
            return PackedString.wrap(bytes32((raw << 8) | 0x2f));
        }
        return PackedString.wrap(PackedStrings.FALLBACK_SENTINEL);
    }

    function change(uint256 next) external returns (uint256) {
        uint256 mode = next % 6;
        bytes32 digest;
        if (mode == 0) {
            // Configure both strings (`_pack` writes both fallback stores).
            packedVersion = _pack(next >> 3);
            packedName = _pack(next >> 6);
            digest = bytes32(next);
        } else if (mode == 1) {
            // The EIP-712 domain shape, hashed.
            digest = keccak256(abi.encode(
                DOMAIN_TYPEHASH, _name(), _version(), block.chainid, address(this)));
        } else if (mode == 2) {
            // Unhashed, mixed with static words and a `bytes` helper.
            bytes memory encoded = abi.encode(next >> 3, _name(), _tag(next >> 3), uint8(next));
            digest = keccak256(encoded) ^ bytes32(encoded.length);
        } else if (mode == 3) {
            // Revert order: a checked `uint8` addition before or after a failing decode.
            uint8 small = uint8(next >> 8);
            if ((next >> 4) % 2 == 0) {
                digest = keccak256(abi.encode(small + 200, _name()));
            } else {
                digest = keccak256(abi.encode(_version(), small + 200, _name()));
            }
        } else if (mode == 4) {
            if ((next >> 3) % 2 == 0) {
                tag = abi.encodePacked(next >> 5, uint8(next));
            } else {
                tag = "";
            }
            digest = keccak256(abi.encode(_tag(next >> 1)));
        } else {
            // Dynamic arguments around a nested hashed encoding of another helper.
            digest = keccak256(abi.encode(
                _tag(next >> 3), next, _name(), keccak256(abi.encode(_version(), next >> 1))));
        }
        saved = uint256(digest);
        return saved;
    }

    function fail() external {
        saved = 77;
        revert();
    }

    // The `eip712Domain()` (ERC-5267) shape: both helpers in a root return tuple.
    function read()
        external
        view
        returns (bytes1, string memory, string memory, uint256, address, bytes32, uint256[] memory)
    {
        return (hex"0f", _name(), _version(), saved, address(this), bytes32(0), new uint256[](0));
    }
}
