// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract ExtCodeHashFixture {
    // keccak256 of the bound runtime `0x5f5ff3` (PUSH0 PUSH0 RETURN).
    bytes32 internal constant BOUND_CODEHASH = 0x17c3092b6f26b342c59b9f80e8d3d8f3ae124106cbd6c0c7f36e6f7951ee0c12;
    // keccak256(""): an existing account without code (EIP-1052).
    bytes32 internal constant EMPTY_CODEHASH = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;

    error UnboundCode();

    uint256 private checks;
    bytes32 private last;
    mapping(address => bytes32) private seen;

    function requireBound(address account) internal view {
        if (account.codehash != BOUND_CODEHASH) revert UnboundCode();
    }

    function codeHash(address account) external view returns (bytes32) {
        return account.codehash;
    }

    function isBound(address account) external view returns (bool) {
        if (account.codehash != BOUND_CODEHASH) revert UnboundCode();
        return true;
    }

    function classify(address account) external view returns (uint256) {
        bytes32 found = account.codehash;
        if (found == bytes32(0)) return 0;
        if (found == EMPTY_CODEHASH) return 1;
        if (found == BOUND_CODEHASH) return 2;
        return 3;
    }

    function sameCode(address left, address right) external view returns (bool) {
        return left.codehash == right.codehash;
    }

    function record(address account) external {
        checks += 1;
        seen[account] = account.codehash;
        last = seen[account];
    }

    function recordBound(address account) external {
        requireBound(account);
        checks += 1;
        last = account.codehash;
    }

    function stored(address account) external view returns (uint256, bytes32, bytes32) {
        return (checks, last, seen[account]);
    }
}
