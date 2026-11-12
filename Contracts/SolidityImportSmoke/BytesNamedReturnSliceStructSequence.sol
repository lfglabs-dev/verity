// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    struct BytePair {
        bytes head;
        bytes tail;
    }

    struct TaggedHead {
        uint256 n;
        bool flag;
        bytes head;
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
        return keccak256(abi.encodePacked(part, uint8(part.length)));
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
        bytes32 c = calldataDigest(data[:end]);
        lastDigest = a ^ b ^ c;
        return lastDigest;
    }

    function bytesStructDigest(bytes calldata data) external returns (bytes32) {
        BytePair memory pair = splitPair(data);
        lastLength = pair.tail.length;
        lastDigest = keccak256(abi.encodePacked(keccak256(splitPair(data).head), pair.tail)) ^ memoryDigest(pair.head);
        return lastDigest;
    }

    // A `bytes memory` parameter reassigned in the helper: solc rebinds only
    // the callee's pointer, so the caller's calldata length and contents stay.
    function grownDigest(bytes memory p) internal pure returns (bytes32) {
        p = abi.encodePacked(p, uint8(1));
        return keccak256(p);
    }

    function concatDigest(bytes memory p) internal pure returns (bytes32) {
        p = bytes.concat(p, hex"02");
        return keccak256(p);
    }

    function parameterReassign(bytes calldata data) external returns (uint256, bytes32, bytes32) {
        bytes memory local = data;
        bytes32 g = grownDigest(data) ^ concatDigest(data) ^ grownDigest(local) ^ grownDigest(data[1:]);
        lastLength = data.length + local.length;
        lastDigest = keccak256(data) ^ keccak256(local);
        return (data.length, keccak256(data), g);
    }

    // An ordinary `bytes memory` local rebound to calldata, to an encoding of
    // itself, and to a slice.
    function localReassign(bytes calldata data, uint256 mode) external returns (bytes32) {
        bytes memory buf = abi.encodePacked(uint8(mode));
        if (mode % 2 == 1) buf = data;
        buf = abi.encodePacked(buf, uint16(buf.length));
        if (mode > 2) buf = data[1:];
        // A `new bytes` local rebound to a calldata copy, then written: the
        // write lands in the copy, not in `data`.
        bytes memory scratch = new bytes(mode % 4 + 1);
        scratch = data;
        if (scratch.length > 0) scratch[0] = bytes1(uint8(mode));
        lastLength = buf.length + scratch.length;
        lastDigest = keccak256(buf) ^ keccak256(scratch) ^ keccak256(data);
        return lastDigest;
    }

    // A named result read before assignment, and rebound to the argument's
    // buffer (solc shares the pointer). Element writes to it fail closed.
    function namedResultAccess(bytes memory part, uint256 mode) internal pure returns (bytes memory out) {
        if (mode == 0) return abi.encodePacked(out, uint8(out.length), keccak256(out));
        out = part;
        if (mode == 1) out = abi.encodePacked(out, uint8(out.length));
    }

    function namedResultAlias(bytes calldata data, uint256 mode) external returns (bytes32, bytes32) {
        bytes memory source = data;
        bytes memory result = namedResultAccess(source, mode);
        lastLength = result.length;
        return (keccak256(source), keccak256(result));
    }

    // Scalar and `bool` members beside `bytes`, a positional constructor, a
    // whole struct passed to a helper, and the struct ABI-encoded.
    function taggedHeadDigest(TaggedHead memory t) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(t.n, t.flag, t.head, uint8(t.head.length)));
    }

    function structMembers(bytes calldata data, uint256 n) external returns (bytes32, bytes32) {
        TaggedHead memory t = TaggedHead(n, n % 2 == 1, data[0:2]);
        BytePair memory pair = BytePair({head: data[0:1], tail: data[1:]});
        lastLength = t.head.length + (t.flag ? 1 : 0) + pair.tail.length;
        return (taggedHeadDigest(t), keccak256(abi.encode(pair)));
    }

    function fail() external {
        total += 1;
        revert("fail");
    }

    function read() external view returns (uint256, bytes32, uint256) {
        return (total, lastDigest, lastLength);
    }
}
