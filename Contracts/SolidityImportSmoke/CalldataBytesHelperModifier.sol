// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract CalldataBytesHelperModifier {
    uint256 private trace;

    function identity(bytes calldata x) private pure returns (bytes calldata) {
        return x;
    }

    function window(bytes calldata x, uint256 start, uint256 end) private pure returns (bytes calldata) {
        return x[start:end];
    }

    function hashPart(bytes calldata x) private pure returns (bytes32) {
        return keccak256(x);
    }

    function copyDigest(bytes memory copy, uint8 tag) private pure returns (bytes32) {
        return keccak256(abi.encodePacked(tag, copy));
    }

    modifier outer(uint256 tag, bytes calldata x, uint256 minLen) {
        require(x.length >= minLen, "short");
        trace = trace * 100 + tag + x.length;
        _;
        trace = trace * 100 + uint8(x[x.length - 1]);
    }

    modifier inner(bytes calldata x, uint256 cut) {
        trace = trace * 100 + uint8(x[0]) + bytes(x[:cut]).length;
        _;
        require(uint8(x[0]) != 255, "post");
        trace = trace * 100 + uint256(uint8(bytes1(bytes4(x[:cut]))));
    }

    function inspect(uint256 tag, bytes calldata data, uint256 start, uint256 end, uint256 cut)
        external
        outer(tag, data, 2)
        inner(data, cut)
        returns (bytes32)
    {
        trace = trace * 100 + identity(data).length;
        trace = trace * 100 + window(data, start, end).length;
        trace = trace * 100 + uint8(window(data, start, end)[0]);
        return hashPart(window(data, start, end)) ^ copyDigest(window(data, start, end), uint8(cut));
    }

    function subSliceInfo(bytes calldata data, uint256 start, uint256 end, uint256 index)
        external
        pure
        returns (uint256 subLen, bytes1 elem, bytes4 prefix, bytes32 subDigest)
    {
        subLen = bytes(window(data, start, end)[1:]).length;
        elem = window(data, start, end)[index];
        prefix = bytes4(window(data, start, end));
        subDigest = keccak256(window(data, start, end)[1:]);
    }

    function sliceModifierArg(bytes calldata data, uint256 start, uint256 end)
        external
        inner(data[start:end], 1)
        returns (uint256)
    {
        trace = trace * 100 + 7;
        return trace;
    }

    function read() external view returns (uint256) {
        return trace;
    }
}

contract CalldataBytesHelperModifierUnsupported {
    function namedHelper(bytes calldata x) private pure returns (bytes calldata out) {
        out = x;
    }

    function useNamedHelper(bytes calldata x) external pure returns (uint256) {
        return namedHelper(x).length;
    }

    function multiStmtHelper(bytes calldata x) private pure returns (bytes calldata) {
        uint256 n = x.length;
        n;
        return x;
    }

    function useMultiStmtHelper(bytes calldata x) external pure returns (uint256) {
        return multiStmtHelper(x).length;
    }

    function msgDataSliceHelper(uint256 start) private pure returns (bytes calldata) {
        return msg.data[start:];
    }

    function useMsgDataSliceHelper(uint256 start) external pure returns (uint256) {
        return msgDataSliceHelper(start).length;
    }

    function reassignHelperParam(bytes calldata x) private pure returns (uint256) {
        x = x[1:];
        return x.length;
    }

    function useReassignHelperParam(bytes calldata x) external pure returns (uint256) {
        return reassignHelperParam(x);
    }

    modifier reassignMod(bytes calldata x) {
        x = x[1:];
        _;
    }

    function useReassignMod(bytes calldata x) external pure reassignMod(x) returns (uint256) {
        return x.length;
    }

    modifier memoryMod(bytes memory x) {
        require(x.length > 0, "empty");
        _;
    }

    function useMemoryMod(bytes calldata x) external pure memoryMod(x) returns (uint256) {
        return x.length;
    }

    modifier calldataMod(bytes calldata x) {
        require(x.length > 0, "empty");
        _;
    }

    function useMsgDataInMod(uint256 v) external pure calldataMod(msg.data) returns (uint256) {
        return v;
    }

    function useMsgDataSliceInMod(uint256 v) external pure calldataMod(msg.data[1:5]) returns (uint256) {
        return v;
    }

    function ident(bytes calldata x) private pure returns (bytes calldata) { return x; }

    function probe(uint256) external pure returns (bytes4) {
        return bytes4(ident(msg.data[1:5]));
    }

    function probeCast(uint256) external pure returns (bytes4) {
        return bytes4(ident(bytes(msg.data[1:5])));
    }

    function nestedDecode(uint256) external pure returns (uint256) {
        return abi.decode(msg.data[:][1:33], (uint256));
    }
}

contract CalldataCopyAndCapture {
    function window(bytes calldata x, uint256 a, uint256 b) private pure returns (bytes calldata) {
        return x[a:b];
    }

    function chainedWindow(bytes calldata x, uint256 a, uint256 b) private pure returns (bytes calldata) {
        return window(x, a, b);
    }

    function read4(bytes calldata x) private pure returns (bytes4) {
        return bytes4(x);
    }

    function ident(bytes calldata x) private pure returns (bytes calldata) {
        return x;
    }

    function readFirstMemWord(bytes memory b) private pure returns (bytes32 w) {
        assembly {
            w := mload(add(b, 32))
        }
    }

    function memSliceWord(bytes calldata x, uint256 a, uint256 b) external pure returns (bytes32, bytes32) {
        uint256 fill = type(uint256).max;
        bytes memory dirty = abi.encode(fill, fill);
        require(keccak256(dirty) != bytes32(0), "dirty");
        bytes memory loc = chainedWindow(x, a, b);
        return (readFirstMemWord(window(x, a, b)), readFirstMemWord(loc));
    }

    modifier checkPostLen(uint256 expected, bytes calldata x) {
        _;
        require(expected == x.length, "post_len");
    }

    function mutateArgInBody(uint256 n, bytes calldata x)
        external
        pure
        checkPostLen(n, x)
        returns (uint256)
    {
        n = 99;
        return n;
    }

    function mutateArgChained(uint256 n, bytes calldata x, uint256 end)
        external
        pure
        checkPostLen(n, chainedWindow(x, 0, end))
        returns (uint256)
    {
        n = 77;
        return n;
    }

    function safeMsgDataSlice(uint256)
        external
        pure
        checkPostLen(32, msg.data[4:])
        returns (bytes4, bytes4, uint256)
    {
        return (read4(msg.data[4:]), bytes4(ident(msg.data[4:])), abi.decode(msg.data[4:], (uint256)));
    }

    function competingAdd(bytes calldata x, uint256 s, uint256 e, uint256 z) external pure returns (uint256) {
        return window(x, s, e).length + (1 / z);
    }

    function competingAddRev(bytes calldata x, uint256 s, uint256 e, uint256 z) external pure returns (uint256) {
        return (1 / z) + window(x, s, e).length;
    }

    function nestedFailures(bytes calldata x, uint256 e, uint256 z) external pure returns (uint256) {
        return window(x, 0, e).length + ((1 / z) + uint8(x[5]));
    }

    function power(bytes calldata x, uint256 e) external pure returns (uint256) {
        return uint256(2) ** window(x, 0, e).length;
    }
}

library CalldataReceiver {
    function take(bytes calldata x, uint256) internal pure returns (bytes calldata) { return x; }
}

type Count is uint256;
function sumCounts(Count a, Count b) pure returns (Count) {
    return Count.wrap(Count.unwrap(a) + Count.unwrap(b));
}
using {sumCounts as +} for Count global;

contract ReceiverOrder {
    using CalldataReceiver for bytes;
    function window(bytes calldata x, uint256 e) private pure returns (bytes calldata) { return x[:e]; }
    function nested(bytes calldata x, uint256 e, uint256 z) external pure returns (uint256) {
        return window(x, e).take(1 / z).length;
    }

    function overloaded(bytes calldata x, uint256 e, uint256 z) external pure returns (uint256) {
        return Count.unwrap(Count.wrap(window(x, e).length) + Count.wrap(1 / z));
    }
}
