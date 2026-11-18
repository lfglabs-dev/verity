// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Root `bytes[] calldata` / `bytes[] memory` parameters (#2701): the array
// is member `w` of the root argument tuple. `data[i]` is a `bytes` value:
// calldata elements are checked lazily at the access (solc's
// `access_calldata_tail`), memory elements are copied eagerly at entry.
contract SequenceFixture {
    uint256 private stored;

    // `data.length` of a root `bytes[] calldata` (the issue's shape).
    function arrayLength(bytes[] calldata data) external returns (uint256) {
        return data.length;
    }

    function lengthAt(bytes[] calldata data, uint256 i) external pure returns (uint256) {
        return data[i].length;
    }

    function hashAt(bytes[] calldata data, uint256 i) external pure returns (bytes32) {
        return keccak256(data[i]);
    }

    function hashAtMemory(bytes[] memory data, uint256 i) external pure returns (bytes32) {
        return keccak256(data[i]);
    }

    function packedAt(bytes[] calldata data, uint256 i) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(data[i], uint8(i)));
    }

    function digestAll(bytes[] calldata data) external returns (bytes32 acc) {
        for (uint256 i = 0; i < data.length; i++) {
            // Encoding arguments must be prelude-free: `data[i]`'s tail checks are hoisted.
            uint256 n = data[i].length;
            bytes32 h = keccak256(data[i]);
            acc = keccak256(abi.encodePacked(acc, n, h));
        }
        stored = data.length;
    }

    function totalLengthMemory(bytes[] memory data) external pure returns (uint256 total) {
        for (uint256 i = 0; i < data.length; i++) {
            total += data[i].length;
        }
    }

    function digest(bytes calldata part) internal pure returns (bytes32) {
        return keccak256(part);
    }

    // The array behind scalar and `bytes` head words, an element passed to a
    // `bytes calldata` helper parameter.
    function afterHead(uint256 a, bytes calldata b, bytes[] calldata data) external pure returns (bytes32) {
        if (data.length == 0) return bytes32(a + b.length);
        return digest(data[data.length - 1]) ^ bytes32(a + b.length);
    }

    function change(uint256 x) external {
        stored = x;
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
