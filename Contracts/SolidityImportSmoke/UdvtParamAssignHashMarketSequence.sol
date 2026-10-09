// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type Clock is uint256;
type ShortId is uint48;

library ClockLib {
    function advance(Clock c, uint256 delta) internal pure returns (Clock) {
        return Clock.wrap(Clock.unwrap(c) + delta);
    }

    function stepValue(Clock c) internal pure returns (uint256) {
        return Clock.unwrap(c);
    }
}

contract SequenceFixture {
    using ClockLib for Clock;

    struct CollateralItem {
        uint256 token;
        uint64 factor;
        bool active;
    }

    struct MarketBundle {
        uint256 baseId;
        CollateralItem[] items;
    }

    bytes32 internal constant ITEM_TYPEHASH =
        keccak256("CollateralItem(uint256 token,uint64 factor,bool active)");

    error UnauthorizedAccess(address caller, uint256 timestamp, uint256 step);
    error InvalidStepInput(uint256 step, address origin);

    event MarketStepRecorded(
        uint256 indexed totalScore,
        bytes32 indexed lastDigest,
        uint256 clockWord,
        uint256 shortTag
    );

    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private lastClockWord;
    uint48 private lastShortTag;

    modifier normalizeCap(uint256 cap) {
        cap = (cap & 0xff) + 5;
        require(cap >= 5, "cap underflow");
        _;
    }

    function _msgSender() internal view returns (address) {
        return msg.sender;
    }

    function _currentStep() internal view returns (uint256) {
        return block.number;
    }

    function _hashTokens(address[] memory tokens) internal pure returns (bytes32 digest) {
        assembly ("memory-safe") {
            digest := keccak256(add(tokens, 0x20), mul(mload(tokens), 0x20))
        }
    }

    function _hashWords(uint256[] memory words) internal pure returns (bytes32 digest) {
        assembly ("memory-safe") {
            digest := keccak256(add(0x20, words), mul(0x20, mload(words)))
        }
    }

    function _hashBytes32Array(bytes32[] memory items) internal pure returns (bytes32 digest) {
        assembly ("memory-safe") {
            digest := keccak256(add(items, 32), mul(mload(items), 32))
        }
    }

    function _scrubAndStep(uint256 step, uint256 bonus) internal pure returns (uint256) {
        step = (step & 0xffff) + 3;
        step = step * 2 + bonus;
        return step;
    }

    function _advanceShortId(ShortId id, uint48 delta) internal pure returns (ShortId) {
        uint48 raw = ShortId.unwrap(id);
        raw = raw + delta;
        return ShortId.wrap(raw);
    }

    function _basePair(uint256 a, uint256 b) internal pure returns (uint256, bytes32) {
        a = a + 7;
        return (a + b, bytes32(a ^ (b << 8)));
    }

    function _chainedPair(uint256 a, uint256 b) internal pure returns (uint256, bytes32) {
        return _basePair(a + 1, b + 2);
    }

    function _branchPair(bool pickChained, uint256 a, uint256 b) internal pure returns (uint256, bytes32) {
        return pickChained ? _chainedPair(a, b) : (a + 100, bytes32(b + 200));
    }

    function _hashCollateralItem(CollateralItem calldata item) internal pure returns (bytes32 digest) {
        uint256 tok = item.token;
        uint256 fac = uint256(item.factor);
        uint256 act = item.active ? 1 : 0;
        bytes32 th = ITEM_TYPEHASH;
        assembly ("memory-safe") {
            mstore(0x00, th)
            mstore(0x20, xor(tok, add(shl(64, fac), act)))
            digest := keccak256(0x00, 0x40)
        }
    }

    function _hashCollateralItemMem(CollateralItem memory item) internal pure returns (bytes32) {
        return keccak256(abi.encode(ITEM_TYPEHASH, item.token, item.factor, item.active));
    }

    function hashMarketBundle(MarketBundle calldata market, Clock clockTag) internal returns (bytes32) {
        clockTag = clockTag.advance(market.baseId & 0xff);
        bytes32[] memory itemHashes = new bytes32[](market.items.length);
        for (uint256 i = 0; i < market.items.length; i++) {
            bytes32 cdHash = _hashCollateralItem(market.items[i]);
            CollateralItem memory memCopy = market.items[i];
            bytes32 memHash = _hashCollateralItemMem(memCopy);
            itemHashes[i] = bytes32(uint256(cdHash) ^ uint256(memHash));
        }
        bytes32 itemsDigest = _hashBytes32Array(itemHashes);
        uint256 cw = clockTag.stepValue();
        lastClockWord = cw;
        lastDigest = bytes32(uint256(itemsDigest) ^ cw ^ market.baseId);
        totalScore += (uint256(lastDigest) & 0xffff) + market.items.length;
        return lastDigest;
    }

    function change(uint256 input) external normalizeCap(input) returns (uint256) {
        if (input == 21) {
            revert InvalidStepInput(_currentStep(), tx.origin);
        }

        uint256 callerCopy = input;
        uint256 scrubbed = _scrubAndStep(callerCopy, 5);
        input = (input & 0xfff) + 11;

        Clock clk = Clock.wrap(input + block.number);
        clk = clk.advance(scrubbed & 0xff);
        uint256 clockWord = clk.stepValue() + callerCopy;

        ShortId sid = ShortId.wrap(uint48(input + 0x1000000000000));
        sid = _advanceShortId(sid, 9);
        uint48 shortTag = ShortId.unwrap(sid);

        address[] memory tokens = new address[](2);
        tokens[0] = _msgSender();
        tokens[1] = address(uint160(0x3000 + (input & 7)));
        bytes32 tokHash = _hashTokens(tokens);

        uint256[] memory words = new uint256[](3);
        words[0] = input;
        words[1] = scrubbed;
        words[2] = clockWord;
        bytes32 wordHash = _hashWords(words);

        (uint256 pairVal, bytes32 pairTag) = _branchPair((input & 1) == 0, input, scrubbed);
        bytes32 combinedDigest = bytes32(uint256(tokHash) ^ uint256(wordHash) ^ uint256(pairTag));

        lastDigest = combinedDigest;
        lastClockWord = clockWord;
        lastShortTag = shortTag;
        uint256 delta = (uint256(combinedDigest) & 0xffffffff) + pairVal + uint256(shortTag);
        totalScore += delta;

        emit MarketStepRecorded(totalScore, lastDigest, lastClockWord, uint256(lastShortTag));
        require(callerCopy != 20, "udvt param assign rollback");
        return totalScore;
    }

    function fail() external {
        totalScore += 999;
        revert UnauthorizedAccess(_msgSender(), block.timestamp, _currentStep());
    }

    function _readSnapshot(bool addBonus) internal view returns (uint256, bytes32, uint256, uint48) {
        uint256 bonus = addBonus ? 10 : 0;
        return (totalScore + bonus, lastDigest, lastClockWord, lastShortTag);
    }

    function read() external view returns (uint256, bytes32, uint256, uint48) {
        return (totalScore & 1) == 0
            ? _readSnapshot(false)
            : (totalScore, lastDigest, lastClockWord, lastShortTag);
    }
}
