// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant MAX_HEIGHT = 3;

bytes32 constant COLLATERAL_PARAMS_TYPEHASH =
    keccak256("CollateralParams(address token,uint256 lltv,uint256 liquidationCursor,address oracle)");

bytes32 constant MARKET_TYPEHASH = keccak256(
    "Market(uint256 chainId,address midnight,address loanToken,CollateralParams[] collateralParams,uint256 maturity,uint256 rcfThreshold,address enterGate,address liquidatorGate)CollateralParams(address token,uint256 lltv,uint256 liquidationCursor,address oracle)"
);

bytes32 constant OFFER_TYPEHASH = keccak256(
    "Offer(Market market,bool buy,address maker,uint256 start,uint256 expiry,uint256 tick,bytes32 group,address callback,bytes callbackData,address receiverIfMakerIsSeller,address ratifier,bool reduceOnly,uint128 maxUnits,uint128 maxAssets,uint256 continuousFeeCap)CollateralParams(address token,uint256 lltv,uint256 liquidationCursor,address oracle)Market(uint256 chainId,address midnight,address loanToken,CollateralParams[] collateralParams,uint256 maturity,uint256 rcfThreshold,address enterGate,address liquidatorGate)"
);

bytes32 constant PRICE_RATIFIER_V1_OFFER_TYPEHASH = keccak256(
    "PriceRatifierV1Offer(Offer offer,address allowedTaker)CollateralParams(address token,uint256 lltv,uint256 liquidationCursor,address oracle)Market(uint256 chainId,address midnight,address loanToken,CollateralParams[] collateralParams,uint256 maturity,uint256 rcfThreshold,address enterGate,address liquidatorGate)Offer(Market market,bool buy,address maker,uint256 start,uint256 expiry,uint256 tick,bytes32 group,address callback,bytes callbackData,address receiverIfMakerIsSeller,address ratifier,bool reduceOnly,uint128 maxUnits,uint128 maxAssets,uint256 continuousFeeCap)"
);

bytes32 constant RATE_RATIFIER_V1_OFFER_TYPEHASH = keccak256(
    "RateRatifierV1Offer(Offer offer,uint256 rate,address allowedTaker)CollateralParams(address token,uint256 lltv,uint256 liquidationCursor,address oracle)Market(uint256 chainId,address midnight,address loanToken,CollateralParams[] collateralParams,uint256 maturity,uint256 rcfThreshold,address enterGate,address liquidatorGate)Offer(Market market,bool buy,address maker,uint256 start,uint256 expiry,uint256 tick,bytes32 group,address callback,bytes callbackData,address receiverIfMakerIsSeller,address ratifier,bool reduceOnly,uint128 maxUnits,uint128 maxAssets,uint256 continuousFeeCap)"
);

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

library HashLib {
    error TreeTooHigh();

    function offerTreeTypeHash(uint256 height) internal pure returns (bytes32) {
        if (height == 0) return keccak256("OfferTree(Offer root,uint256 nonce)");
        if (height == 1) return keccak256("OfferTree(Offer[2] root,uint256 nonce)");
        if (height == 2) return keccak256("OfferTree(Offer[2][2] root,uint256 nonce)");
        if (height == 3) return keccak256("OfferTree(Offer[2][2][2] root,uint256 nonce)");
        revert TreeTooHigh();
    }

    function priceRatifierV1OfferTreeTypeHash(uint256 height) internal pure returns (bytes32) {
        if (height == 0) return keccak256("PriceRatifierV1OfferTree(PriceRatifierV1Offer root,uint256 maxBlockNumber)");
        if (height == 1) return keccak256("PriceRatifierV1OfferTree(PriceRatifierV1Offer[2] root,uint256 maxBlockNumber)");
        if (height == 2) return keccak256("PriceRatifierV1OfferTree(PriceRatifierV1Offer[2][2] root,uint256 maxBlockNumber)");
        if (height == 3) return keccak256("PriceRatifierV1OfferTree(PriceRatifierV1Offer[2][2][2] root,uint256 maxBlockNumber)");
        revert TreeTooHigh();
    }

    function rateRatifierV1OfferTreeTypeHash(uint256 height) internal pure returns (bytes32) {
        if (height == 0) return keccak256("RateRatifierV1OfferTree(RateRatifierV1Offer root,uint256 maxBlockNumber)");
        if (height == 1) return keccak256("RateRatifierV1OfferTree(RateRatifierV1Offer[2] root,uint256 maxBlockNumber)");
        if (height == 2) return keccak256("RateRatifierV1OfferTree(RateRatifierV1Offer[2][2] root,uint256 maxBlockNumber)");
        if (height == 3) return keccak256("RateRatifierV1OfferTree(RateRatifierV1Offer[2][2][2] root,uint256 maxBlockNumber)");
        revert TreeTooHigh();
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

    function hashNode(bytes32 left, bytes32 right) internal pure returns (bytes32) {
        return keccak256(abi.encode(left, right));
    }

    function hashCollateralParams(CollateralParams memory collateralParams) internal pure returns (bytes32) {
        return keccak256(
            abi.encode(
                COLLATERAL_PARAMS_TYPEHASH,
                collateralParams.token,
                collateralParams.lltv,
                collateralParams.liquidationCursor,
                collateralParams.oracle
            )
        );
    }

    function hashMarket(Market memory market) internal pure returns (bytes32) {
        bytes memory encodedCollateralParams;
        for (uint256 i = 0; i < market.collateralParams.length; i++) {
            encodedCollateralParams = bytes.concat(
                encodedCollateralParams,
                hashCollateralParams(market.collateralParams[i])
            );
        }

        return keccak256(
            abi.encode(
                MARKET_TYPEHASH,
                market.chainId,
                market.midnight,
                market.loanToken,
                keccak256(encodedCollateralParams),
                market.maturity,
                market.rcfThreshold,
                market.enterGate,
                market.liquidatorGate
            )
        );
    }

    function hashOffer(Offer memory offer) internal pure returns (bytes32) {
        return keccak256(
            abi.encode(
                OFFER_TYPEHASH,
                hashMarket(offer.market),
                offer.buy,
                offer.maker,
                offer.start,
                offer.expiry,
                offer.tick,
                offer.group,
                offer.callback,
                keccak256(offer.callbackData),
                offer.receiverIfMakerIsSeller,
                offer.ratifier,
                offer.reduceOnly,
                offer.maxUnits,
                offer.maxAssets,
                offer.continuousFeeCap
            )
        );
    }

    function hashPriceRatifierV1Offer(Offer memory offer, address allowedTaker) internal pure returns (bytes32) {
        return keccak256(abi.encode(PRICE_RATIFIER_V1_OFFER_TYPEHASH, hashOffer(offer), allowedTaker));
    }

    function hashRateRatifierV1Offer(Offer memory offer, uint256 rate, address allowedTaker) internal pure returns (bytes32) {
        return keccak256(abi.encode(RATE_RATIFIER_V1_OFFER_TYPEHASH, hashOffer(offer), rate, allowedTaker));
    }
}

contract SequenceFixture {
    bytes32 internal constant EIP712_DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)");
    bytes32 internal constant ENTER_TYPEHASH =
        keccak256("Enter(bytes32 marketId,address sender,address receiver,uint256 maxExpiry,uint256 nonce)");

    mapping(bytes32 => uint256) private offerCounts;
    mapping(address => uint256) private nonces;
    bytes32 private lastOfferDigest;
    bytes32 private lastMarketHash;
    uint256 private lastCallbackLen;

    function DOMAIN_SEPARATOR() public view returns (bytes32) {
        return keccak256(abi.encode(EIP712_DOMAIN_TYPEHASH, block.chainid, address(this)));
    }

    function change(uint256 input) external returns (uint256, uint256) {
        if (input == 19) {
            return (uint256(HashLib.offerTreeTypeHash(MAX_HEIGHT + 1)), 0);
        }
        if (input == 21) {
            return (0, uint256(HashLib.priceRatifierV1OfferTreeTypeHash(MAX_HEIGHT + 1)));
        }
        if (input == 23) {
            return (uint256(HashLib.rateRatifierV1OfferTreeTypeHash(MAX_HEIGHT + 1)), 0);
        }

        uint256 height = input % (MAX_HEIGHT + 1);
        bytes32 treeHash = HashLib.offerTreeTypeHash(height);
        bytes32 priceTreeHash = HashLib.priceRatifierV1OfferTreeTypeHash(height);
        bytes32 rateTreeHash = HashLib.rateRatifierV1OfferTreeTypeHash(height);
        bytes32 combinedTree = HashLib.hashNode(treeHash, HashLib.hashNode(priceTreeHash, rateTreeHash));

        CollateralParams memory cp = CollateralParams({
            token: address(uint160(0x1000 + (input % 7))),
            lltv: 8000 + (input % 500),
            liquidationCursor: 2000 + (input % 300),
            oracle: address(uint160(0x2000 + (input % 5)))
        });
        bytes32 cpHash = HashLib.hashCollateralParams(cp);

        uint256 nonce = nonces[msg.sender]++;
        uint256 maxExpiry = block.timestamp + height;
        bytes32 enterStructHash = keccak256(
            abi.encode(ENTER_TYPEHASH, combinedTree, msg.sender, cp.token, maxExpiry, nonce)
        );
        bytes32 enterDigest = keccak256(bytes.concat("\x19\x01", DOMAIN_SEPARATOR(), enterStructHash));

        offerCounts[combinedTree] += 1;
        lastOfferDigest = enterDigest;
        lastMarketHash = cpHash;
        lastCallbackLen = height;

        require(input != 20, "offer hash rollback");
        return (
            (uint256(enterDigest) & 0xFFFFFFFFFFFFFFFF) + offerCounts[combinedTree] + nonce,
            (uint256(cpHash) & 0xFFFFFFFFFFFFFFFF) + height
        );
    }

    function fail() external {
        nonces[msg.sender] = 999;
        lastOfferDigest = bytes32(uint256(888));
        lastMarketHash = HashLib.offerTreeTypeHash(MAX_HEIGHT + 2);
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        bytes32 dom = DOMAIN_SEPARATOR();
        return (
            uint256(lastOfferDigest) & 0xFFFFFFFFFFFFFFFF,
            uint256(lastMarketHash) & 0xFFFFFFFFFFFFFFFF,
            nonces[msg.sender] + lastCallbackLen * 100,
            uint256(dom) & 0xFFFFFFFFFFFFFFFF
        );
    }

    function inspectOfferMem(Offer memory offer, uint256 rate) external returns (uint256, uint256) {
        bytes32 rHash = HashLib.hashRateRatifierV1Offer(offer, rate, offer.ratifier);
        bytes32 digest = keccak256(bytes.concat("\x19\x01", DOMAIN_SEPARATOR(), rHash));

        uint256 cpBonus = offer.market.collateralParams.length;
        if (cpBonus > 0) {
            CollateralParams memory firstCp = offer.market.collateralParams[0];
            cpBonus += firstCp.lltv + (uint256(HashLib.hashCollateralParams(firstCp)) & 0xFFFF);
        }

        uint256 cbBonus = offer.callbackData.length + (uint256(keccak256(offer.callbackData)) & 0xFFFF);
        uint256 flagBonus = (offer.buy ? 10 : 20) + (offer.reduceOnly ? 100 : 200)
            + uint256(offer.maxUnits) + uint256(offer.maxAssets) + offer.market.chainId;

        offerCounts[rHash] += 1;
        lastOfferDigest = digest;
        lastMarketHash = rHash;
        lastCallbackLen = offer.callbackData.length;

        return (
            (uint256(digest) & 0xFFFFFFFFFFFFFFFF)
                + cpBonus
                + offerCounts[rHash],
            (uint256(rHash) & 0xFFFFFFFFFFFFFFFF)
                + cbBonus
                + flagBonus
        );
    }

    function inspectOfferCd(Offer calldata offer, uint256 rate, address allowedTaker) external returns (uint256, uint256) {
        bytes32 mHash = HashLib.hashMarket(offer.market);
        bytes32 pHash = HashLib.hashPriceRatifierV1Offer(offer, allowedTaker);
        bytes32 digest = keccak256(bytes.concat("\x19\x01", DOMAIN_SEPARATOR(), pHash));

        uint256 cpBonus = offer.market.collateralParams.length;
        if (cpBonus > 0) {
            CollateralParams memory firstCp = offer.market.collateralParams[0];
            cpBonus += firstCp.liquidationCursor + (uint256(HashLib.hashCollateralParams(firstCp)) & 0xFFFF);
        }

        uint256 cbBonus = offer.callbackData.length + (uint256(keccak256(offer.callbackData)) & 0xFFFF) + rate;
        uint256 flagBonus = (offer.buy ? 1 : 2) + (offer.reduceOnly ? 3 : 4)
            + uint256(offer.maxUnits) + uint256(offer.maxAssets) + offer.market.maturity;

        offerCounts[pHash] += 1;
        lastOfferDigest = digest;
        lastMarketHash = mHash;
        lastCallbackLen = offer.callbackData.length;

        return (
            (uint256(digest) & 0xFFFFFFFFFFFFFFFF)
                + cpBonus
                + offerCounts[pHash],
            (uint256(mHash) & 0xFFFFFFFFFFFFFFFF)
                + cbBonus
                + flagBonus
        );
    }
}
