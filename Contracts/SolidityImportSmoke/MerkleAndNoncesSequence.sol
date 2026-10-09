// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

bytes32 constant COLLATERAL_PARAMS_TYPEHASH = 0x39ed3f928d24fd00574b1a02aba9c2483abcf5d9a3a366118c9a5aa29885b841;
bytes32 constant EIP712_DOMAIN_TYPEHASH = 0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218;
bytes32 constant CALLBACK_SUCCESS = keccak256("morpho.midnight.callbackSuccess");
int256 constant LN_ONE_PLUS_DELTA = 9999500033329732;
int256 constant NEGATIVE_SLOPE = -125;
address constant DEFAULT_TREASURY = address(0x000000000000000000000000000000000000dEaD);

contract SequenceFixture {
    error InvalidAccountNonce(address account, uint256 currentNonce);
    error LeafIndexOutOfRange();
    event MerkleNonceObserved(uint256 indexed totalScore, bytes32 rootDigest, uint256 usedNonce);

    struct CounterBox {
        uint128 hits;
        uint128 misses;
    }

    uint256 private totalScore;
    uint128 private stepCount;
    int256 private signedCursor;
    bytes32 private lastRoot;
    mapping(address => uint256) private _nonces;
    mapping(uint256 => mapping(uint256 => uint256)) private gridNonce;
    mapping(uint256 => CounterBox) private boxes;

    function _hashNode(bytes32 left, bytes32 right) internal pure returns (bytes32 value) {
        assembly ("memory-safe") {
            mstore(0x00, left)
            mstore(0x20, right)
            value := keccak256(0x00, 0x40)
        }
    }

    function _hashSingle0(bytes32 word) internal pure returns (bytes32 value) {
        assembly ("memory-safe") {
            mstore(0x00, word)
            value := keccak256(0x00, 0x20)
        }
    }

    function _hashSingle32(bytes32 word) internal pure returns (bytes32 value) {
        assembly ("memory-safe") {
            mstore(0x20, word)
            value := keccak256(0x20, 0x20)
        }
    }

    function _hashPair(bytes32 a, bytes32 b) private pure returns (bytes32) {
        return a < b ? _hashNode(a, b) : _hashNode(b, a);
    }

    function _domainSeparator() internal view returns (bytes32) {
        return keccak256(abi.encode(EIP712_DOMAIN_TYPEHASH, block.chainid, address(this)));
    }

    function _useNonce(address owner) internal returns (uint256) {
        unchecked {
            return _nonces[owner]++;
        }
    }

    function _useCheckedNonce(address owner, uint256 nonce) internal {
        uint256 current = _useNonce(owner);
        if (nonce != current) {
            revert InvalidAccountNonce(owner, current);
        }
    }

    function _foldProof2(bytes32 leafHash, uint256 leafIndex, bytes32 p0, bytes32 p1)
        internal
        pure
        returns (bytes32)
    {
        require(leafIndex >> 2 == 0, LeafIndexOutOfRange());
        bytes32 currentHash = leafHash;
        currentHash = (leafIndex & 1) == 0 ? _hashNode(currentHash, p0) : _hashNode(p0, currentHash);
        currentHash = ((leafIndex >> 1) & 1) == 0 ? _hashNode(currentHash, p1) : _hashNode(p1, currentHash);
        return _hashPair(currentHash, CALLBACK_SUCCESS);
    }

    function change(uint256 input) external returns (uint256) {
        address owner = (input & 1) == 0 ? msg.sender : DEFAULT_TREASURY;
        if (input == 21) {
            _useCheckedNonce(owner, 999999);
        }

        uint256 expectedNonce = _nonces[owner];
        _useCheckedNonce(owner, expectedNonce);
        uint256 afterFirst = ++_nonces[owner];
        uint256 beforeDec = _nonces[owner]--;
        uint256 score = expectedNonce + afterFirst + beforeDec;

        uint256 localCounter = (input & 0xff) + 3;
        uint256 postInc = localCounter++;
        uint256 preInc = ++localCounter;
        uint256 postDec = localCounter--;
        uint256 preDec = --localCounter;
        localCounter++;
        --localCounter;
        score += postInc + preInc + postDec + preDec + localCounter;

        uint64 narrowLocal = uint64((input & 0x3f) + 2);
        uint64 narrowPost = narrowLocal++;
        uint64 narrowPre = ++narrowLocal;
        unchecked {
            narrowLocal--;
        }
        score += uint256(narrowPost) + uint256(narrowPre) + uint256(narrowLocal);

        uint256 preStep = ++stepCount;
        uint256 postStep = stepCount++;
        if (stepCount > 5) {
            stepCount--;
        }
        score += preStep + postStep;

        int256 sDelta = LN_ONE_PLUS_DELTA + NEGATIVE_SLOPE + int256(uint256(input & 0x7f));
        int256 sPost = sDelta++;
        int256 sPre = --sDelta;
        signedCursor = sDelta;
        signedCursor++;
        int256 cursorSnap = --signedCursor;
        score += uint256(sPost + sPre + cursorSnap) & 0xffffffff;

        uint256 boxKey = input & 3;
        uint128 hitBefore = boxes[boxKey].hits++;
        uint128 hitAfter = ++boxes[boxKey].hits;
        boxes[boxKey].misses++;
        if (boxes[boxKey].misses > 2) {
            --boxes[boxKey].misses;
        }
        score += uint256(hitBefore) + uint256(hitAfter) + uint256(boxes[boxKey].misses);

        uint256 g1 = input & 1;
        uint256 g2 = (input >> 1) & 1;
        uint256 gridBefore = gridNonce[g1][g2]++;
        uint256 gridAfter = ++gridNonce[g1][g2];
        gridNonce[g1][g2]--;
        score += gridBefore + gridAfter + (uint256(uint160(DEFAULT_TREASURY)) & 0xffff);

        bytes32 leaf = _hashSingle0(bytes32(input ^ uint256(COLLATERAL_PARAMS_TYPEHASH)));
        bytes32 sib0 = _hashSingle32(bytes32(input + expectedNonce + 1));
        bytes32 sib1 = _domainSeparator();
        sib0 <<= (input & 7);
        sib1 >>= ((input >> 3) & 7);
        bytes32 shiftedMask = (COLLATERAL_PARAMS_TYPEHASH << 3) ^ (CALLBACK_SUCCESS >> 2);
        bytes32 merkleOut = _foldProof2(leaf, input & 3, sib0, sib1 ^ shiftedMask);
        lastRoot = merkleOut;

        totalScore += (uint256(merkleOut) & 0xffffffff) + score;
        emit MerkleNonceObserved(totalScore, lastRoot, _nonces[owner]);
        require(input != 20, "merkle nonces rollback");
        return totalScore;
    }

    function fail() external {
        stepCount++;
        totalScore += 999;
        revert InvalidAccountNonce(DEFAULT_TREASURY, 404);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        uint256 summary = uint256(stepCount) + uint256(signedCursor & 0xffff) + _nonces[DEFAULT_TREASURY]
            + uint256(boxes[0].hits) + uint256(boxes[1].hits) + gridNonce[0][0] + gridNonce[1][0];
        return (totalScore, lastRoot, summary);
    }
}
