// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    struct BytePair {
        bytes head;
        bytes tail;
    }

    uint256 private total;
    bytes32 private lastDigest;
    uint256 private lastLength;

    function taggedDigest(bytes memory input, uint8 domain) internal pure returns (bytes memory out) {
        out = abi.encodePacked(domain, keccak256(input));
    }

    function maybeEncoded(uint256 x) internal pure returns (bytes memory out) {
        if (x % 3 == 0) return out;
        if (x % 3 == 1) {
            out = abi.encodePacked(uint32(x));
        }
    }

    function copied(bytes memory part) internal pure returns (bytes memory out) {
        out = part;
    }

    function calldataDigest(bytes calldata part) internal pure returns (bytes32) {
        return keccak256(part);
    }

    function memoryDigest(bytes memory part) internal pure returns (bytes32) {
        bytes32 first = keccak256(abi.encodePacked(part, uint8(part.length)));
        part = abi.encodePacked(uint8(9));
        return first ^ keccak256(abi.encodePacked(part, uint8(part.length)));
    }

    function splitPair(bytes calldata data) internal pure returns (BytePair memory) {
        return BytePair({head: data[0:4], tail: data[4:data.length]});
    }

    function change(uint256 x) external returns (uint256) {
        bytes memory encoded = maybeEncoded(x);
        bytes memory tagged = taggedDigest(encoded, uint8(x));
        lastLength = encoded.length;
        lastDigest = keccak256(tagged);
        total += encoded.length + 1;
        return total;
    }

    function namedReturnCopy(bytes calldata data) external pure returns (bytes memory out) {
        out = data;
    }

    function namedReturnEarly(bytes calldata data, uint256 mode) external pure returns (bytes memory out) {
        if (mode == 0) return out;
        out = abi.encodePacked(data, uint8(mode));
        if (mode == 1) return out;
        if (mode == 2) {
            out = copied(data[1:]);
            return out;
        }
        out = taggedDigest(out, uint8(mode));
    }

    function sliceArgumentDigest(bytes calldata data, uint256 start, uint256 end) external returns (bytes32) {
        bytes32 a = calldataDigest(data[start:end]);
        bytes32 b = memoryDigest(data[start:]);
        bytes32 c = calldataDigest(data[:end]) ^ memoryDigest(msg.data[0:4]);
        lastDigest = a ^ b ^ c ^ keccak256(abi.encodePacked(data, uint8(data.length)));
        return lastDigest;
    }

    function bytesStructDigest(bytes calldata data) external returns (bytes32) {
        BytePair memory pair = splitPair(data);
        lastLength = pair.tail.length;
        lastDigest = keccak256(abi.encodePacked(keccak256(splitPair(data).head), pair.tail)) ^ memoryDigest(pair.head);
        return lastDigest;
    }

    function fail() external {
        total += 1;
        revert("fail");
    }

    function read() external view returns (uint256, bytes32, uint256) {
        return (total, lastDigest, lastLength);
    }
}
