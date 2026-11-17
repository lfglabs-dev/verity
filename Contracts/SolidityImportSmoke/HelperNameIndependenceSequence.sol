// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// An internal helper is modeled by its own body, whatever its name or arity.
// The helper name below once selected a fixed keccak256 shim in place of the body.
contract SequenceFixture {
    bytes32 private key;
    uint256 private count;
    function calculatePositionKey(address owner, int24 lower, int24 upper, bytes32 salt)
        internal
        pure
        returns (bytes32)
    {
        uint256 ticks = (uint256(uint24(upper)) << 24) | uint256(uint24(lower));
        return bytes32((uint256(uint160(owner)) << 48) | ticks) ^ salt;
    }
    function change(uint256 x) external returns (bytes32) {
        int24 lower = int24(int256(x % 1000)) - 500;
        int24 upper = lower + int24(int256((x >> 10) % 100));
        key = calculatePositionKey(address(uint160(x >> 96)), lower, upper, bytes32(x << 200));
        count += 1;
        return key;
    }
    function fail() external {
        count = 0;
        revert();
    }
    function read() external view returns (bytes32, uint256) {
        return (key, count);
    }
}
