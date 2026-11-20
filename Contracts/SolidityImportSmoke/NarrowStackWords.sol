// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract NarrowStackWords {
    uint256 private first;
    uint256 private second;

    uint8 public constant narrowConstant = uint8(uint256(257));

    function payableCopy(uint256 x) external pure returns (uint256 word) {
        address payable a = payable(address(uint160(x)));
        address b = a;
        assembly { word := b }
    }

    function rawBytes(uint256 x) internal pure returns (bytes4 b) {
        assembly { b := x }
    }

    function invertedBytes(uint256 x) external pure returns (uint256 word) {
        bytes4 b = ~rawBytes(x);
        assembly { word := b }
    }

    function shiftUntilZero(uint8 a) external pure returns (uint256 n) {
        uint8 b = a;
        while (b != 0) { ++n; b >>= 1; }
    }

    error WideError(uint256 argument);
    function widenedError(uint8 a) external pure { revert WideError(a); }
    function explicitWideError(uint8 a) external pure { revert WideError(uint256(a)); }
    function constantError() external pure { revert NarrowError(narrowConstant); }

    function bytesCast(bytes32 x) external pure returns (uint256 word) {
        bytes4 b = bytes4(x);
        assembly { word := b }
    }

    function bytesLocal(uint256 x) external pure returns (uint256 word) {
        bytes4 b;
        assembly { b := x }
        bytes4 q = ~b;
        assembly { word := q }
    }

    function bytesChoice(uint256 x) external pure returns (bytes32) {
        bytes4 b = ~bytes4(bytes32(x));
        return x == 0 ? b : bytes32(x);
    }

    function bytesArrayOr(uint256 x) external pure returns (uint256 elemWord, uint256 stackWord) {
        bytes4 v;
        assembly { v := x }
        bytes4[] memory s = new bytes4[](1);
        s[0] |= v;
        bytes4 elem = s[0];
        v |= 0x00000001;
        assembly {
            elemWord := elem
            stackWord := v
        }
    }

    function returnedBytesLiteral() external pure returns (bytes4) {
        return 0x11223344;
    }

    function returnedBytesTuple() external pure returns (bytes4, uint256) {
        return (0x11223344, 1);
    }

    function signedWidening(uint256 x) external pure returns (uint256 widened, uint256 rawCopy) {
        int8 v = 0;
        assembly { v := x }
        int256 w = v;
        int8 copy = v;
        assembly { rawCopy := copy }
        widened = uint256(w);
    }

    function rawPayable(uint256 x) internal pure returns (address payable p) {
        assembly { p := x }
    }

    function rawAddress(uint256 x) internal pure returns (address a) {
        assembly { a := x }
    }

    function payableCasts(uint256 x) external pure returns (uint256 fromAddress, uint256 fromPayable) {
        address payable firstCast = payable(rawAddress(x));
        address payable secondCast = payable(rawPayable(x));
        assembly {
            fromAddress := firstCast
            fromPayable := secondCast
        }
    }

    function addressChoice(uint256 x, bool flag) external pure returns (uint256 word) {
        address payable p = rawPayable(x);
        address a = flag ? p : address(0);
        assembly { word := a }
    }

    function constantCopy() external pure returns (uint256 word) {
        uint8 a = narrowConstant;
        assembly { word := a }
    }

    function checkedValue(uint256 x, uint256 n) external pure returns (uint256) {
        uint8 a; uint8 count;
        assembly { a := x count := n }
        return (a >> count) + uint8(1);
    }

    function shiftedCopy(uint256 x, uint256 n) external pure returns (uint256 word) {
        uint8 a; uint8 count;
        assembly { a := x count := n }
        a <<= count;
        uint8 copy = a;
        assembly { word := copy }
    }

    function overwrite(uint256 x, bool reset) external pure returns (uint256 word) {
        uint8 a;
        assembly { a := x }
        unchecked { a += 2; }
        if (reset) a = 7;
        assembly { word := a }
    }

    error NarrowError(uint8 argument);

    function widen(uint8 a) internal pure returns (uint256) { return a; }

    function boundaries(uint256 x) external pure returns (uint8, uint256, uint256) {
        uint8 a;
        assembly { a := x }
        bytes memory payload = abi.encode(a);
        uint256 encoded;
        assembly { encoded := mload(add(payload, 32)) }
        return (a, widen(a), encoded);
    }

    function errorValue(uint256 x) external pure {
        uint8 a;
        assembly { a := x }
        revert NarrowError(a);
    }

    function literalArray(uint256 x) external pure returns (uint256 word) {
        uint8 a;
        assembly { a := x }
        uint8[1] memory elements = [a];
        uint8 b = elements[0];
        assembly { word := b }
    }

    function signaturePayload(uint256 x) external pure returns (bytes32) {
        uint8 a;
        assembly { a := x }
        return keccak256(abi.encodeWithSignature("f(uint8)", a));
    }

    function signedCast(uint256 x) external pure returns (uint256 word) {
        uint8 a;
        assembly { a := x }
        int8 b = int8(a);
        assembly { word := b }
    }

    function returnedLiteral(uint256 x) external pure returns (uint8[1] memory) {
        uint8 a;
        assembly { a := x }
        return [a];
    }

    event Signed(int8 argument);

    function logSigned(uint256 x) external {
        int8 a = 0;
        assembly { a := x }
        emit Signed(a);
    }

    function fromAssembly(uint256 x) internal pure returns (uint8 a) {
        assembly { a := x }
    }

    function copiedResult(uint256 x) external pure returns (uint256 word) {
        uint8 a = fromAssembly(x);
        assembly { word := a }
    }

    function addressCast(uint256 x) external pure returns (uint256 word) {
        address a = address(uint160(x));
        assembly { word := a }
    }

    function square(uint8 x) external pure returns (uint8) {
        return x ** uint8(2);
    }

    uint8 private stored;

    function storeAndCopy(uint256 x) external returns (uint256 word, uint256 slotWord) {
        uint8 a;
        assembly { a := x }
        uint8 b = (stored = a);
        assembly { word := b slotWord := sload(stored.slot) }
    }

    function quotient(uint256 x, uint256 y) external pure returns (uint256 word) {
        int8 a = 0; int8 b = 0;
        assembly { a := x b := y }
        unchecked {
            int8 q = a / b;
            assembly { word := q }
        }
    }

    mapping(uint256 => uint256) private data;

    function literalKey() external returns (uint256) {
        data[1] = 11;
        data[257] = 22;
        return data[uint8(uint256(257))];
    }

    function narrowCount(uint256 x) external pure returns (uint256 n) {
        uint8 limit;
        assembly { limit := x }
        for (uint256 i = 0; i < limit; ++i) n += 1;
    }

    function descending(uint256 x) external pure returns (uint256 n) {
        uint8 start;
        assembly { start := x }
        for (uint8 i = start; i > 0; --i) ++n;
    }

    function descendingWords(uint256 x) external pure returns (uint256 a, uint256 b, uint256 n) {
        uint8 start;
        assembly { start := x }
        unchecked {
            for (uint8 i = start; i > 0; --i) {
                if (n == 0) { assembly { a := i } }
                if (n == 1) { assembly { b := i } }
                ++n;
            }
        }
    }

    function narrowSlice(bytes calldata input, uint256 x) external pure returns (bytes32) {
        uint8 start;
        assembly { start := x }
        return keccak256(input[start:]);
    }

    function carried(uint256 x) external pure returns (uint256 word) {
        uint8 a; uint8 copy;
        assembly { a := x }
        for (uint256 i = 0; i < 2; ++i) {
            copy = a;
            unchecked { a += 2; }
        }
        assembly { word := copy }
    }

    event NarrowEvent(uint128 value);
    function badEmit(uint8 x) external { emit NarrowEvent(x); }

    function receiveWord(bytes4 arg) external pure { require(arg == 0x11223344); }
    function tryBytesLiteral() external returns (uint256) {
        try this.receiveWord(0x11223344) { return 1; } catch { return 0; }
    }

    function prefixInc(uint8 x) external returns (uint256 word, uint256 slotWord) {
        stored = x;
        unchecked {
            uint8 r = ++stored;
            assembly { word := r slotWord := sload(stored.slot) }
        }
    }

    function prefixDec(uint8 x) external returns (uint256 word, uint256 slotWord) {
        stored = x;
        unchecked {
            uint8 r = --stored;
            assembly { word := r slotWord := sload(stored.slot) }
        }
    }

    function receivePair(uint8 first, uint8 second) external pure { require(first < second); }
    function namedTry() external returns (uint256) {
        try this.receivePair({second: 2, first: 1}) { return 1; } catch { return 0; }
    }
}
