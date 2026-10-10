// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant MAX_HEIGHT = 3;

struct CollateralParams {
    address token;
    uint256 lltv;
    uint256 liquidationCursor;
    address oracle;
}

struct Market {
    uint256 chainId;
    address midnight;
    address loanToken;
    CollateralParams[] collateralParams;
    uint256 maturity;
    uint256 rcfThreshold;
    address enterGate;
    address liquidatorGate;
}

struct Offer {
    Market market;
    bool buy;
    address maker;
    uint256 start;
    uint256 expiry;
    uint256 tick;
    bytes32 group;
    address callback;
    bytes callbackData;
    address receiverIfMakerIsSeller;
    address ratifier;
    bool reduceOnly;
    uint128 maxUnits;
    uint128 maxAssets;
    uint256 continuousFeeCap;
}

struct RatifierConfig {
    uint256 minRate;
    address allowedTaker;
    bool active;
    bytes4 tag;
}

library RatifierHashLib {
    error TreeTooHigh();

    function hashNode(bytes32 left, bytes32 right) internal pure returns (bytes32) {
        return keccak256(abi.encode(left, right));
    }

    function computeRoot(bytes32 leafHash, uint256 leafIndex, bytes32[] memory proof) internal pure returns (bytes32) {
        if (proof.length > MAX_HEIGHT) return bytes32(0);
        bytes32 hash = leafHash;
        for (uint256 i = 0; i < proof.length; ++i) {
            bool isRight = (leafIndex >> i) & 1 == 1;
            hash = isRight ? hashNode(proof[i], hash) : hashNode(hash, proof[i]);
        }
        return hash;
    }

    function isLeaf(bytes32 root, bytes32 leafHash, uint256 leafIndex, bytes32[] memory proof) internal pure returns (bool) {
        if (proof.length > MAX_HEIGHT) return false;
        if (leafIndex >= (1 << proof.length)) return false;

        bytes32 hash = leafHash;
        for (uint256 i = 0; i < proof.length; ++i) {
            bool isRight = (leafIndex >> i) & 1 == 1;
            hash = isRight ? hashNode(proof[i], hash) : hashNode(hash, proof[i]);
        }

        return hash == root;
    }
}

contract SequenceFixture {
    error NotTheMaker();
    error ExpiredTree();
    error InvalidLeaf();
    error RateTooLow();

    mapping(address => mapping(bytes32 => uint256)) public maxBlockNumber;
    mapping(bytes32 => uint256) private ratifiedCounts;
    bytes private storedPayload;
    bytes32 private lastRatifiedRoot;
    uint256 private lastDecodedRate;

    function _decodeStoredHeader() internal view returns (RatifierConfig memory) {
        return abi.decode(storedPayload, (RatifierConfig));
    }

    function _decodeUintArray(bytes memory raw) internal pure returns (uint256[] memory) {
        return abi.decode(raw, (uint256[]));
    }

    function _firstOrZero(uint256[] memory xs) internal pure returns (uint256) {
        return xs.length == 0 ? 0 : xs[0];
    }

    function change(uint256 input) external returns (uint256, uint256) {
        uint256 minRate = 1000 + (input % 500);
        address allowedTaker = address(uint160(0x3000 + (input % 11)));
        bool active = (input & 1) == 0;
        bytes4 tag = bytes4(keccak256(abi.encode(input)));

        bytes memory encodedConfig = abi.encode(minRate, allowedTaker, active, tag);
        storedPayload = encodedConfig;

        RatifierConfig memory cfg = _decodeStoredHeader();
        uint256 directMinRate = abi.decode(encodedConfig, (RatifierConfig)).minRate;

        (uint256 tupRate, , bool tupActive, bytes4 tupTag) =
            abi.decode(storedPayload, (uint256, address, bool, bytes4));

        uint256 shiftedInput = (input % 1000) + 77;
        bytes memory singleBuf = abi.encode(shiftedInput);
        uint256 singleDecoded = abi.decode(singleBuf, (uint256));
        bytes memory arrBuf = abi.encode(uint256(0x20), uint256(1), shiftedInput);
        uint256[] memory arrDecoded = _decodeUintArray(arrBuf);
        uint256 inlineElem = _firstOrZero(abi.decode(arrBuf, (uint256[])));
        uint256 extraWord = singleDecoded + arrDecoded[0] + inlineElem;
        bytes32 root = keccak256(
            abi.encode(cfg.minRate, cfg.allowedTaker, tupActive, tupTag, extraWord)
        );

        maxBlockNumber[msg.sender][root] = block.number + (input % 17);
        ratifiedCounts[root] += 1;
        lastRatifiedRoot = root;
        lastDecodedRate = cfg.minRate + directMinRate + tupRate;

        require(input != 20, "ratifier change rollback");
        return (
            lastDecodedRate + ratifiedCounts[root],
            (uint256(root) & 0xFFFFFFFFFFFFFFFF) + maxBlockNumber[msg.sender][root]
        );
    }

    function decodeMixedPayload(bytes calldata raw, uint256 rateFloor) external returns (uint256, uint256) {
        (RatifierConfig memory cfg, uint256[] memory weights, bytes memory extraBytes, string memory label) =
            abi.decode(raw, (RatifierConfig, uint256[], bytes, string));

        if (cfg.minRate < rateFloor) revert RateTooLow();

        uint256 weightSum = weights.length;
        for (uint256 i = 0; i < weights.length; ++i) {
            weightSum += weights[i];
        }

        bytes32 extraHash = keccak256(bytes.concat(extraBytes, bytes(label)));
        uint256 bonus = extraBytes.length + bytes(label).length + (cfg.active ? 11 : 22);

        storedPayload = extraBytes;
        ratifiedCounts[extraHash] += 1;
        lastRatifiedRoot = extraHash;
        lastDecodedRate = cfg.minRate + weightSum;

        return (
            lastDecodedRate + bonus + ratifiedCounts[extraHash],
            (uint256(extraHash) & 0xFFFFFFFFFFFFFFFF) + (uint256(uint32(cfg.tag)))
        );
    }

    function ratifyOfferCd(Offer calldata offer, bytes32 root, uint256 actualRate) external returns (uint256, uint256) {
        (uint256 minRate, address allowedTaker, uint256 leafIndex, bytes32[] memory proof) =
            abi.decode(offer.callbackData, (uint256, address, uint256, bytes32[]));

        if (allowedTaker != address(0) && allowedTaker != msg.sender) {
            revert NotTheMaker();
        }
        if (actualRate < minRate) {
            revert RateTooLow();
        }

        bytes32 leafHash = keccak256(abi.encode(offer.maker, offer.tick, minRate, allowedTaker));
        bytes32 targetRoot = root == bytes32(0)
            ? RatifierHashLib.computeRoot(leafHash, leafIndex % 8, proof)
            : root;
        if (!RatifierHashLib.isLeaf(targetRoot, leafHash, leafIndex % 8, proof)) {
            revert InvalidLeaf();
        }

        ratifiedCounts[targetRoot] += 1;
        lastRatifiedRoot = targetRoot;
        lastDecodedRate = actualRate - minRate + proof.length;

        return (
            lastDecodedRate + ratifiedCounts[targetRoot],
            (uint256(leafHash) & 0xFFFFFFFFFFFFFFFF) + offer.market.collateralParams.length
        );
    }

    function fail() external {
        lastDecodedRate = 9999;
        bytes memory badBool = abi.encode(uint256(2));
        bool flag = abi.decode(badBool, (bool));
        if (flag) {
            lastDecodedRate = 1;
        }
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        return (
            uint256(lastRatifiedRoot) & 0xFFFFFFFFFFFFFFFF,
            lastDecodedRate,
            storedPayload.length,
            maxBlockNumber[msg.sender][lastRatifiedRoot]
        );
    }
}
