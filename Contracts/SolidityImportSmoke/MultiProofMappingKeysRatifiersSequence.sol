// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IOracleFeed {
    function latestAnswer() external view returns (int256);
}

contract SequenceFixture {
    enum GateMode {
        Disabled,
        Whitelist,
        Public
    }

    error InvalidMultiProof(uint256 leavesLength, uint256 flagsLength);
    error UnauthorizedRatifier(address caller);
    event MultiProofRatified(uint256 indexed totalScore, bytes32 rootDigest, address indexed oracle, bool enabled);

    struct RatifierData {
        IOracleFeed oracle;
        uint88 maxPercentageDifference;
        bool enabled;
        bytes32 lastDigest;
        int256 signedDelta;
    }

    uint256 private totalScore;
    bytes32 private lastMultiRoot;
    address private lastTransientActor;

    mapping(bytes32 => RatifierData) private ratifiers;
    mapping(address => mapping(address => bool)) private isWhitelisted;
    mapping(uint64 => uint256) private narrowKeyScores;
    mapping(int256 => uint256) private signedKeyScores;
    mapping(bool => uint256) private boolKeyScores;
    mapping(GateMode => uint256) private modeKeyScores;
    mapping(IOracleFeed => uint256) private feedKeyScores;

    function _hashNode(bytes32 left, bytes32 right) internal pure returns (bytes32 value) {
        assembly ("memory-safe") {
            mstore(0x00, left)
            mstore(0x20, right)
            value := keccak256(0x00, 0x40)
        }
    }

    function _hashPair(bytes32 a, bytes32 b) private pure returns (bytes32) {
        return a < b ? _hashNode(a, b) : _hashNode(b, a);
    }

    function _tExchange(bytes32 slot, address value) internal returns (address oldValue) {
        assembly ("memory-safe") {
            oldValue := tload(slot)
            tstore(slot, value)
        }
    }

    function _tGet(bytes32 slot) internal view returns (address value) {
        assembly ("memory-safe") {
            value := tload(slot)
        }
    }

    function _processMultiProof(
        bytes32[] memory proof,
        bool[] memory proofFlags,
        bytes32[] memory leaves
    ) internal pure returns (bytes32 merkleRoot) {
        uint256 leavesLen = leaves.length;
        uint256 proofFlagsLen = proofFlags.length;
        if (leavesLen + proof.length != proofFlagsLen + 1) {
            revert InvalidMultiProof(leavesLen, proofFlagsLen);
        }
        bytes32[] memory hashes = new bytes32[](proofFlagsLen);
        uint256 leafPos = 0;
        uint256 hashPos = 0;
        uint256 proofPos = 0;
        for (uint256 i = 0; i < proofFlagsLen; i++) {
            bytes32 a = leafPos < leavesLen ? leaves[leafPos++] : hashes[hashPos++];
            bytes32 b = proofFlags[i]
                ? (leafPos < leavesLen ? leaves[leafPos++] : hashes[hashPos++])
                : proof[proofPos++];
            hashes[i] = _hashPair(a, b);
        }
        if (proofFlagsLen > 0) {
            if (proofPos != proof.length) {
                revert InvalidMultiProof(leavesLen, proofFlagsLen);
            }
            unchecked {
                return hashes[proofFlagsLen - 1];
            }
        } else if (leavesLen > 0) {
            return leaves[0];
        } else {
            return bytes32(0);
        }
    }

    function change(uint256 input) external returns (address resultAddr) {
        if (input == 21) {
            bytes32[] memory badLeaves = new bytes32[](1);
            bytes32[] memory badProof = new bytes32[](1);
            bool[] memory badFlags = new bool[](2);
            _processMultiProof(badProof, badFlags, badLeaves);
        }

        bytes32[] memory leaves = new bytes32[](2);
        leaves[0] = bytes32(input ^ 0xaaaa01);
        leaves[1] = bytes32((input + 19) ^ 0xbbbb02);

        bytes32[] memory proof = new bytes32[](1);
        proof[0] = bytes32((input * 5 + 3) ^ 0xcccc03);

        bool[] memory flags = new bool[](2);
        flags[0] = true;
        flags[1] = false;

        bytes32 root = _processMultiProof(proof, flags, leaves);
        lastMultiRoot = root;

        bytes32 ratifierId = bytes32(input & 3);
        IOracleFeed feed = IOracleFeed(address(uint160(0x1000 + (input & 7))));
        uint88 maxDiff = uint88(((input & 0xff) + 10) * 100);
        bool isEnabled = (input & 2) == 0;
        int256 delta = int256(input & 0x7f) - 40;

        ratifiers[ratifierId].oracle = feed;
        ratifiers[ratifierId].maxPercentageDifference = maxDiff;
        ratifiers[ratifierId].enabled = isEnabled;
        ratifiers[ratifierId].lastDigest = root;
        ratifiers[ratifierId].signedDelta = delta;

        if ((input & 4) != 0) {
            delete ratifiers[ratifierId].enabled;
        }

        address user = address(uint160(0x2000 + (input & 3)));
        isWhitelisted[msg.sender][user] = isEnabled;
        uint64 nKey = uint64((input & 7) + 1);
        narrowKeyScores[nKey] += uint256(maxDiff);
        signedKeyScores[delta] += (input & 0x1f) + 1;
        boolKeyScores[ratifiers[ratifierId].enabled] += 3;
        GateMode mode = (input & 1) == 0 ? GateMode.Whitelist : GateMode.Public;
        modeKeyScores[mode] += 5;
        feedKeyScores[ratifiers[ratifierId].oracle] += 7;

        bytes32 tSlot = bytes32(uint256(0x9100 + (input & 1)));
        address nextActor = address(uint160(uint256(root) ^ uint256(uint160(address(feed)))));
        address prevActor = _tExchange(tSlot, nextActor);
        address loadedActor = _tGet(tSlot);
        lastTransientActor = loadedActor;

        uint256 score = (uint256(root) & 0xffffffff)
            + uint256(uint160(address(ratifiers[ratifierId].oracle)))
            + uint256(ratifiers[ratifierId].maxPercentageDifference)
            + (ratifiers[ratifierId].enabled ? 100 : 10)
            + (isWhitelisted[msg.sender][user] ? 50 : 5)
            + narrowKeyScores[nKey]
            + signedKeyScores[delta]
            + boolKeyScores[true]
            + modeKeyScores[mode]
            + feedKeyScores[feed]
            + uint256(uint160(prevActor))
            + (uint256(uint24(uint256(ratifiers[ratifierId].signedDelta))) & 0xffff);

        totalScore += score;
        emit MultiProofRatified(totalScore, lastMultiRoot, address(ratifiers[ratifierId].oracle), ratifiers[ratifierId].enabled);
        require(input != 20, "multiproof ratifiers rollback");

        bytes32 exitSlot = bytes32(uint256(0x9200));
        uint256 dirtyWord = totalScore | (uint256(0xfeedface) << 160);
        assembly ("memory-safe") {
            tstore(exitSlot, dirtyWord)
            resultAddr := tload(exitSlot)
        }
    }

    function fail() external {
        totalScore += 999;
        address caller = msg.sender;
        revert UnauthorizedRatifier(caller);
    }

    function read() external view returns (uint256, bytes32, address, bool) {
        bytes32 r0 = bytes32(uint256(0));
        uint256 summary = totalScore
            + uint256(ratifiers[r0].maxPercentageDifference)
            + boolKeyScores[true]
            + boolKeyScores[false]
            + modeKeyScores[GateMode.Whitelist]
            + modeKeyScores[GateMode.Public];
        return (summary, lastMultiRoot, address(ratifiers[r0].oracle), ratifiers[r0].enabled);
    }
}
