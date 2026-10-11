// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type ShortString is bytes32;

library StorageSlotSlice38 {
    struct StringSlot {
        string value;
    }

    struct BytesSlot {
        bytes value;
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

library MathSlice38 {
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10 ** 64) {
                value /= 10 ** 64;
                result += 64;
            }
            if (value >= 10 ** 32) {
                value /= 10 ** 32;
                result += 32;
            }
            if (value >= 10 ** 16) {
                value /= 10 ** 16;
                result += 16;
            }
            if (value >= 10 ** 8) {
                value /= 10 ** 8;
                result += 8;
            }
            if (value >= 10 ** 4) {
                value /= 10 ** 4;
                result += 4;
            }
            if (value >= 10 ** 2) {
                value /= 10 ** 2;
                result += 2;
            }
            if (value >= 10 ** 1) {
                result += 1;
            }
        }
        return result;
    }

    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        uint256 isGt;
        unchecked {
            isGt = value > (1 << 128) - 1 ? 1 : 0;
            value >>= isGt * 128;
            result += isGt * 16;

            isGt = value > (1 << 64) - 1 ? 1 : 0;
            value >>= isGt * 64;
            result += isGt * 8;

            isGt = value > (1 << 32) - 1 ? 1 : 0;
            value >>= isGt * 32;
            result += isGt * 4;

            isGt = value > (1 << 16) - 1 ? 1 : 0;
            value >>= isGt * 16;
            result += isGt * 2;

            result += value > (1 << 8) - 1 ? 1 : 0;
        }
        return result;
    }
}

library StringsSlice38 {
    bytes16 private constant HEX_DIGITS = "0123456789abcdef";
    uint8 private constant ADDRESS_LENGTH = 20;

    error StringsInsufficientHexLength(uint256 value, uint256 length);

    function toString(uint256 value) internal pure returns (string memory) {
        unchecked {
            uint256 length = MathSlice38.log10(value) + 1;
            string memory buffer = new string(length);
            uint256 ptr;
            assembly ("memory-safe") {
                ptr := add(buffer, add(32, length))
            }
            while (true) {
                ptr--;
                assembly ("memory-safe") {
                    mstore8(ptr, byte(mod(value, 10), HEX_DIGITS))
                }
                value /= 10;
                if (value == 0) break;
            }
            return buffer;
        }
    }

    function toHexString(uint256 value) internal pure returns (string memory) {
        unchecked {
            return toHexString(value, MathSlice38.log256(value) + 1);
        }
    }

    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        unchecked {
            uint256 localValue = value;
            uint256 hexLen = 2 * length;
            bytes memory buffer = new bytes(hexLen + 2);
            uint256 ptr;
            assembly ("memory-safe") {
                mstore8(add(buffer, 32), 0x30)
                mstore8(add(buffer, 33), 0x78)
                ptr := add(buffer, add(34, hexLen))
            }
            for (uint256 i = 0; i < hexLen; ++i) {
                ptr--;
                assembly ("memory-safe") {
                    mstore8(ptr, byte(and(localValue, 0xf), HEX_DIGITS))
                }
                localValue >>= 4;
            }
            if (localValue != 0) {
                revert StringsInsufficientHexLength(value, length);
            }
            return string(buffer);
        }
    }

    function toHexString(address addr) internal pure returns (string memory) {
        return toHexString(uint256(uint160(addr)), ADDRESS_LENGTH);
    }
}

library ShortStringsSlice38 {
    bytes32 private constant FALLBACK_SENTINEL = 0x00000000000000000000000000000000000000000000000000000000000000FF;

    error StringTooLong(uint256 length);
    error InvalidShortString();

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
            StorageSlotSlice38.getStringSlot(store).value = value;
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

abstract contract BaseUriTokenSlice38 {
    using StringsSlice38 for uint256;

    uint256 internal _baseMode;

    function _baseURI() internal view virtual returns (string memory) {
        return _baseMode == 0 ? "" : "ipfs://base/";
    }

    function tokenURI(uint256 tokenId) public view virtual returns (string memory) {
        string memory baseURI = _baseURI();
        return bytes(baseURI).length > 0 ? string.concat(baseURI, tokenId.toString()) : "";
    }
}

contract SequenceFixture is BaseUriTokenSlice38 {
    using StringsSlice38 for uint256;
    using StringsSlice38 for address;

    event MetadataUpdate(uint256 _tokenId);
    event ScopedPayloadRecorded(address indexed owner, uint256 indexed tokenId, bytes32 payloadDigest, uint256 uriLen);

    mapping(uint256 tokenId => string) private _tokenURIs;
    mapping(uint256 tokenId => string) public publicTokenURIs;
    mapping(address owner => mapping(uint256 tokenId => bytes)) public scopedPayloads;

    ShortString private _fallbackTag;
    string private _fallbackTagStore;
    uint256 private totalScore;
    bytes32 private lastUriHash;

    function tokenURI(uint256 tokenId) public view virtual override returns (string memory) {
        string storage _tokenURI = _tokenURIs[tokenId];
        string memory base = _baseURI();

        if (bytes(base).length == 0) {
            return _tokenURI;
        }
        if (bytes(_tokenURI).length > 0) {
            return string.concat(base, _tokenURI);
        }

        return super.tokenURI(tokenId);
    }

    function _setTokenURI(uint256 tokenId, string memory _tokenURI) internal virtual {
        _tokenURIs[tokenId] = _tokenURI;
        publicTokenURIs[tokenId] = _tokenURI;
        emit MetadataUpdate(tokenId);
    }

    function _clearTokenURI(uint256 tokenId) internal {
        if (bytes(_tokenURIs[tokenId]).length != 0) {
            delete _tokenURIs[tokenId];
            delete publicTokenURIs[tokenId];
        }
    }

    function _writeScopedPayload(bytes storage slot, bytes memory payload) internal {
        StorageSlotSlice38.getBytesSlot(slot).value = payload;
    }

    function _storedUriLength(string storage uriRef) internal view returns (uint256) {
        return bytes(uriRef).length;
    }

    function formatDecimal(uint256 value) public pure returns (string memory) {
        return value.toString();
    }

    function formatHex(uint256 value) public pure returns (string memory) {
        return value.toHexString();
    }

    function formatAddress(address account) public pure returns (string memory) {
        return account.toHexString();
    }

    function readFallbackTag() public view returns (string memory) {
        return ShortStringsSlice38.toStringWithFallback(_fallbackTag, _fallbackTagStore);
    }

    function readFallbackTagLength() public view returns (uint256) {
        return ShortStringsSlice38.byteLengthWithFallback(_fallbackTag, _fallbackTagStore);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 tokenId = (input & 0x07) + 1;
        _baseMode = input & 1;

        string memory decStr = ((input & 0xffffffff) + 17).toString();
        string memory hexStr = ((input & 0xfff) + 0x10).toHexString(2);

        if ((input & 3) == 0) {
            _setTokenURI(tokenId, string.concat("item-", decStr, "-", hexStr));
        } else if ((input & 3) == 1) {
            _setTokenURI(tokenId, "0123456789abcdef0123456789abcdef-long-uri-payload");
        } else if ((input & 3) == 2) {
            _clearTokenURI(tokenId);
        }

        if ((input & 4) == 0) {
            _fallbackTag = ShortStringsSlice38.toShortStringWithFallback("short-tag", _fallbackTagStore);
        } else {
            _fallbackTag = ShortStringsSlice38.toShortStringWithFallback(
                "0123456789abcdef0123456789abcdef-fallback",
                _fallbackTagStore
            );
        }

        uint8 b0 = uint8(0x41 + (input & 0x0f));
        uint8 b1 = uint8(0x61 + ((input >> 4) & 0x0f));
        bytes memory rawBuf = abi.encodePacked(
            b0,
            b1,
            uint8(tokenId),
            uint8(_baseMode)
        );

        bytes storage payloadSlot = scopedPayloads[msg.sender][tokenId];
        if ((input & 8) == 0) {
            _writeScopedPayload(payloadSlot, rawBuf);
        } else {
            delete scopedPayloads[msg.sender][tokenId];
        }

        string memory resolvedUri = tokenURI(tokenId);
        string memory resolvedTag = ShortStringsSlice38.toStringWithFallback(_fallbackTag, _fallbackTagStore);
        uint256 tagLen = ShortStringsSlice38.byteLengthWithFallback(_fallbackTag, _fallbackTagStore);
        uint256 storedLen = _storedUriLength(_tokenURIs[tokenId]);
        uint256 payloadLen = scopedPayloads[msg.sender][tokenId].length;

        bytes32 uriDigest = keccak256(bytes(resolvedUri));
        bytes32 tagDigest = keccak256(bytes(resolvedTag));
        bytes32 payloadDigest = keccak256(scopedPayloads[msg.sender][tokenId]);

        emit ScopedPayloadRecorded(msg.sender, tokenId, payloadDigest, bytes(resolvedUri).length);

        uint256 delta;
        unchecked {
            delta =
                (uint256(uriDigest) & 0xffffffff) +
                (uint256(tagDigest) & 0xffff) +
                (uint256(payloadDigest) & 0xffff) +
                tagLen * 100 +
                storedLen * 10 +
                payloadLen;
            totalScore += delta;
        }
        lastUriHash = uriDigest ^ tagDigest ^ payloadDigest;
        require(input != 20, "SBM: rollback");
        return totalScore;
    }

    function fail() external {
        _setTokenURI(99, "reverted-uri");
        totalScore += 555;
        revert("SBM: fail");
    }

    function read() external view returns (uint256, bytes32, uint256, uint256) {
        return (
            totalScore,
            lastUriHash,
            ShortStringsSlice38.byteLengthWithFallback(_fallbackTag, _fallbackTagStore),
            bytes(_tokenURIs[1]).length
        );
    }
}
