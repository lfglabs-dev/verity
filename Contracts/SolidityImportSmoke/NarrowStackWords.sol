// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract NarrowStackWords {
    uint256 private first;
    uint256 private second;

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
}
