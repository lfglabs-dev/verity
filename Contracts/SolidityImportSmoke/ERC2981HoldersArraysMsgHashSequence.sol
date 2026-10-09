// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type ShortString is bytes32;

interface IERC165Lite {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface IERC2981Lite {
    function royaltyInfo(uint256 tokenId, uint256 salePrice)
        external
        view
        returns (address receiver, uint256 royaltyAmount);
}

interface IERC721ReceiverLite {
    function onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes calldata data
    ) external returns (bytes4);
}

interface IERC1155ReceiverLite {
    function onERC1155Received(
        address operator,
        address from,
        uint256 id,
        uint256 value,
        bytes calldata data
    ) external returns (bytes4);

    function onERC1155BatchReceived(
        address operator,
        address from,
        uint256[] calldata ids,
        uint256[] calldata values,
        bytes calldata data
    ) external returns (bytes4);
}

contract SequenceFixture {
    struct RoyaltyInfo {
        address receiver;
        uint96 royaltyFraction;
    }

    error ERC2981InvalidDefaultRoyalty(uint256 numerator, uint256 denominator);
    error ERC2981InvalidDefaultRoyaltyReceiver(address receiver);
    error ERC2981InvalidTokenRoyalty(uint256 tokenId, uint256 numerator, uint256 denominator);
    error ERC2981InvalidTokenRoyaltyReceiver(uint256 tokenId, address receiver);
    error RoyaltySequenceRollback();

    event RoyaltyStepRecorded(
        uint256 indexed totalScore,
        bytes32 indexed lastDigest,
        address royaltyReceiver,
        uint256 royaltyAmount,
        uint256 holderSelectorWord
    );

    RoyaltyInfo private _defaultRoyaltyInfo;
    mapping(uint256 => RoyaltyInfo) private _tokenRoyaltyInfo;
    uint256 private totalScore;
    bytes32 private lastDigest;
    address private lastReceiver;
    uint256 private lastRoyaltyAmount;
    uint32 private lastSelectorWord;

    function _feeDenominator() internal pure returns (uint96) {
        return 10000;
    }

    function supportsInterface(bytes4 interfaceId) public view returns (bool) {
        return
            interfaceId == type(IERC2981Lite).interfaceId ||
            interfaceId == type(IERC1155ReceiverLite).interfaceId ||
            interfaceId == type(IERC165Lite).interfaceId;
    }

    function onERC721Received(
        address,
        address,
        uint256,
        bytes memory
    ) public virtual returns (bytes4) {
        return this.onERC721Received.selector;
    }

    function onERC1155Received(
        address,
        address,
        uint256,
        uint256,
        bytes memory
    ) public virtual returns (bytes4) {
        return this.onERC1155Received.selector;
    }

    function onERC1155BatchReceived(
        address,
        address,
        uint256[] memory,
        uint256[] memory,
        bytes memory
    ) public virtual returns (bytes4) {
        return this.onERC1155BatchReceived.selector;
    }

    function royaltyInfo(uint256 tokenId, uint256 salePrice)
        public
        view
        returns (address receiver, uint256 amount)
    {
        RoyaltyInfo memory royalty = _tokenRoyaltyInfo[tokenId];
        if (royalty.receiver == address(0)) {
            royalty = _defaultRoyaltyInfo;
        }
        receiver = royalty.receiver;
        amount = (salePrice * royalty.royaltyFraction) / _feeDenominator();
    }

    function _setDefaultRoyalty(address receiver, uint96 feeNumerator) internal {
        uint256 denominator = _feeDenominator();
        if (feeNumerator > denominator) {
            revert ERC2981InvalidDefaultRoyalty(feeNumerator, denominator);
        }
        if (receiver == address(0)) {
            revert ERC2981InvalidDefaultRoyaltyReceiver(address(0));
        }
        _defaultRoyaltyInfo = RoyaltyInfo(receiver, feeNumerator);
    }

    function _deleteDefaultRoyalty() internal {
        delete _defaultRoyaltyInfo;
    }

    function _setTokenRoyalty(uint256 tokenId, address receiver, uint96 feeNumerator) internal {
        uint256 denominator = _feeDenominator();
        if (feeNumerator > denominator) {
            revert ERC2981InvalidTokenRoyalty(tokenId, feeNumerator, denominator);
        }
        if (receiver == address(0)) {
            revert ERC2981InvalidTokenRoyaltyReceiver(tokenId, address(0));
        }
        _tokenRoyaltyInfo[tokenId] = RoyaltyInfo(receiver, feeNumerator);
    }

    function _resetTokenRoyalty(uint256 tokenId) internal {
        delete _tokenRoyaltyInfo[tokenId];
    }

    function _unsafeMemoryAccessUint(uint256[] memory arr, uint256 pos)
        internal
        pure
        returns (uint256 res)
    {
        assembly {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }

    function _unsafeMemoryAccessAddress(address[] memory arr, uint256 pos)
        internal
        pure
        returns (address res)
    {
        assembly {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }

    function _toEthSignedMessageHash(bytes32 messageHash)
        internal
        pure
        returns (bytes32 digest)
    {
        assembly ("memory-safe") {
            mstore(0x00, "\x19Ethereum Signed Message:\n32")
            mstore(0x1c, messageHash)
            digest := keccak256(0x00, 0x3c)
        }
    }

    function _toDataWithIntendedValidatorHash(
        address validator,
        bytes memory data
    ) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"19_00", validator, data));
    }

    function _toTypedDataHash(bytes32 domainSeparator, bytes32 structHash)
        internal
        pure
        returns (bytes32 digest)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, hex"19_01")
            mstore(add(ptr, 0x02), domainSeparator)
            mstore(add(ptr, 0x22), structHash)
            digest := keccak256(ptr, 0x42)
        }
    }

    function _shortStringByteLength(ShortString s) internal pure returns (uint256) {
        uint256 result = uint256(ShortString.unwrap(s)) & 0xFF;
        return result;
    }

    function royaltyAndHolderCheck(uint256 tokenId, uint256 salePrice)
        external
        returns (address, uint256, bytes4, bytes32)
    {
        (address receiver, uint256 royaltyAmount) = royaltyInfo(tokenId, salePrice);
        bytes4 sel721 = onERC721Received(msg.sender, receiver, tokenId, "ok");
        bytes4 sel1155 = IERC1155ReceiverLite.onERC1155Received.selector;
        bytes4 combinedSel = sel721 ^ sel1155 ^ this.onERC1155BatchReceived.selector;

        bytes32 ethDigest = _toEthSignedMessageHash(bytes32(salePrice ^ tokenId));
        bytes32 validatorDigest = _toDataWithIntendedValidatorHash(
            receiver,
            abi.encodePacked(tokenId, salePrice, combinedSel)
        );
        bytes32 typedDigest = _toTypedDataHash(ethDigest, validatorDigest);

        lastDigest = typedDigest;
        lastReceiver = receiver;
        lastRoyaltyAmount = royaltyAmount;
        lastSelectorWord = uint32(combinedSel);
        totalScore += (uint256(typedDigest) & 0xffff) + royaltyAmount + uint256(lastSelectorWord & 0xff);
        emit RoyaltyStepRecorded(totalScore, lastDigest, lastReceiver, lastRoyaltyAmount, uint256(lastSelectorWord));
        return (receiver, royaltyAmount, combinedSel, typedDigest);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 tokenId = input & 3;
        address candidate = address(uint160(0x5000 + (input & 7)));
        uint96 fraction = uint96(((input & 0x3f) * 100) % 9000 + 100);

        if (input == 21) {
            _setDefaultRoyalty(candidate, 10001);
        }

        uint256 mode = input % 4;
        if (mode == 0) {
            _setDefaultRoyalty(candidate, fraction);
            _setTokenRoyalty(tokenId, address(uint160(0x6000 + (input & 7))), uint96(fraction / 2 + 50));
        } else if (mode == 1) {
            _setDefaultRoyalty(candidate, fraction);
            _resetTokenRoyalty(tokenId);
        } else if (mode == 2) {
            _setTokenRoyalty(tokenId, candidate, fraction);
            _deleteDefaultRoyalty();
        } else {
            _defaultRoyaltyInfo.receiver = candidate;
            _defaultRoyaltyInfo.royaltyFraction = fraction;
            _resetTokenRoyalty(tokenId);
        }

        uint256 salePrice = ((input & 0xff) + 1) * 1000;
        (address rcv, uint256 amt) = royaltyInfo(tokenId, salePrice);

        uint256[] memory amounts = new uint256[](2);
        amounts[0] = salePrice;
        amounts[1] = amt + uint256(_defaultRoyaltyInfo.royaltyFraction) + 17;

        address[] memory receivers = new address[](2);
        receivers[0] = candidate;
        receivers[1] = rcv;

        uint256 pickedAmt = _unsafeMemoryAccessUint(amounts, 1);
        address pickedRcv = _unsafeMemoryAccessAddress(receivers, 1);

        ShortString ss = ShortString.wrap(bytes32((input & 0x1f) | (uint256(0x414243) << 232)));
        uint256 ssLen = _shortStringByteLength(ss);

        bytes4 sel = this.onERC721Received.selector ^
            this.onERC1155Received.selector ^
            IERC1155ReceiverLite.onERC1155BatchReceived.selector;

        bytes32 ethDigest = _toEthSignedMessageHash(bytes32(pickedAmt + ssLen));
        bytes32 valDigest = _toDataWithIntendedValidatorHash(
            pickedRcv,
            abi.encodePacked(tokenId, pickedAmt, sel)
        );
        bytes32 typedDigest = _toTypedDataHash(ethDigest, valDigest);

        lastDigest = typedDigest;
        lastReceiver = pickedRcv;
        lastRoyaltyAmount = pickedAmt + ssLen;
        lastSelectorWord = uint32(sel);

        uint256 delta = (uint256(typedDigest) & 0xffffffff) +
            lastRoyaltyAmount +
            (uint256(uint160(pickedRcv)) & 0xffff) +
            uint256(lastSelectorWord & 0xffff);
        totalScore += delta;

        emit RoyaltyStepRecorded(totalScore, lastDigest, lastReceiver, lastRoyaltyAmount, uint256(lastSelectorWord));
        require(input != 20, "erc2981 holders arrays msghash rollback");
        return totalScore;
    }

    function fail() external {
        _setDefaultRoyalty(msg.sender, 500);
        totalScore += 777;
        if (msg.sender != address(0)) {
            revert RoyaltySequenceRollback();
        }
    }

    function read() external view returns (uint256, bytes32, address, uint256, bytes4) {
        uint256 defFrac = uint256(_defaultRoyaltyInfo.royaltyFraction);
        return (totalScore + defFrac, lastDigest, lastReceiver, lastRoyaltyAmount, bytes4(lastSelectorWord));
    }
}
