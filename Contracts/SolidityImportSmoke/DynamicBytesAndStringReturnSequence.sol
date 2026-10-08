// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IReturnTarget {
    function exec(address caller, uint256 amount, int256 delta) external returns (bool);
}

contract SequenceFixture {
    error DynamicReturnBlocked(uint256 input, bytes32 digest, uint256 returnCount);
    event DynamicReturnObserved(uint256 indexed totalScore, bytes32 digest, uint256 lengthMetric);

    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private returnCount;

    modifier trackReturn(uint256 delta) {
        returnCount += 1;
        _;
        totalScore += (delta & 0xffff) + returnCount;
    }

    function _concat(string memory _a, string memory _b) internal pure returns (string memory) {
        return string(abi.encodePacked(_a, _b));
    }

    function _packPayload(bytes memory payload, bytes32 salt) internal pure returns (bytes memory) {
        return abi.encodePacked(payload, salt, hex"c0ffee");
    }

    function change(uint256 input) external returns (uint256) {
        string memory label = _concat("vault:", "tranche");
        bytes32 saltWord = bytes32((input & 0xffffffff) + 1);
        bytes memory packed = _packPayload(abi.encode(input), saltWord);
        uint256 combinedLen = bytes(label).length + packed.length;
        bytes32 digest = keccak256(abi.encodePacked(label, packed));

        if (input == 21) {
            revert DynamicReturnBlocked(input, digest, combinedLen);
        }

        returnCount += 1;
        uint256 metric = combinedLen + returnCount;
        totalScore += (uint256(digest) & 0xffffffff) + metric;
        lastDigest = digest;
        emit DynamicReturnObserved(totalScore, lastDigest, metric);
        require(input != 20, "dynamic return rollback");
        return totalScore;
    }

    function concatStrings(
        string memory a,
        string calldata b,
        uint256 mode
    ) external trackReturn(mode) returns (string memory) {
        uint256 lenSum = bytes(a).length + bytes(b).length;
        bytes32 digest = keccak256(abi.encodePacked(a, ":", b, mode));
        lastDigest = digest;
        totalScore += (uint256(digest) & 0xffffffff) + lenSum;
        emit DynamicReturnObserved(totalScore, lastDigest, lenSum);

        uint256 kind = mode % 4;
        if (kind == 0) {
            return _concat(a, b);
        } else if (kind == 1) {
            return string.concat(a, "-", b);
        } else if (kind == 2) {
            return a;
        } else if (bytes(b).length == 0) {
            return "fallback-empty";
        } else {
            return b;
        }
    }

    function buildPayload(
        bytes memory memPart,
        bytes calldata cdPart,
        uint256 mode
    ) external trackReturn(mode) returns (bytes memory) {
        uint256 lenSum = memPart.length + cdPart.length;
        bytes32 modeTag = bytes32((mode & 0xffffffff) + 3);
        int256 signedDelta = int256(mode & 0xff) - 10;
        bytes32 digest = keccak256(abi.encodePacked(memPart, cdPart, mode));
        lastDigest = digest;
        totalScore += (uint256(digest) & 0xffffffff) + lenSum;
        emit DynamicReturnObserved(totalScore, lastDigest, lenSum);

        uint256 kind = mode % 5;
        if (kind == 0) {
            return _packPayload(memPart, modeTag);
        } else if (kind == 1) {
            return abi.encodeCall(
                IReturnTarget.exec,
                (msg.sender, mode, signedDelta)
            );
        } else if (kind == 2) {
            return abi.encode(mode, modeTag);
        } else if (kind == 3) {
            return memPart;
        } else if (cdPart.length == 0) {
            return hex"deadbeef01";
        } else {
            return cdPart;
        }
    }

    function fail() external {
        totalScore += 999;
        string memory errLabel = _concat("err:", "revert");
        bytes32 d = keccak256(bytes(errLabel));
        uint256 errLen = bytes(errLabel).length;
        revert DynamicReturnBlocked(999, d, errLen);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        return (totalScore, lastDigest, returnCount);
    }
}
