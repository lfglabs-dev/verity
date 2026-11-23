// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Internal helpers returning `string memory` / `bytes memory` among several results,
// bound by a tuple declaration or a tuple assignment. Each result position is its own
// buffer; solc (legacy and via-IR) copies only the pointer, so a helper returning one
// buffer twice gives two aliases, and a returned parameter aliases the caller's buffer:
// a later element write through the caller's local is visible through the result.
// change(x) selects a case by c = x % 8 with n = x / 8:
//   0: (bool, bytes) of length n (0, 31, 32, 33, 40; above 40 the helper reverts),
//      after the helper's storage write;
//   1: unnamed (string, string) of literals;
//   2: named (string, string) assigned in the body (a short or a 57-byte name);
//   3: one `new bytes` buffer returned twice;
//   4: a returned parameter, written through the caller's local afterwards;
//   5: a buffer built from storage before the caller's later storage write;
//   6: tuple assignment to a helper's named (string, string) results;
//   7: `return helper(n)` forwarding (bool, bytes) from another helper.
contract SequenceFixture {
    error TooLong(uint256 n);

    uint256 internal counter;
    bool internal lastOk;
    uint256 internal lastLen;
    bytes32 internal lastHash;
    bytes32 internal otherHash;

    function sized(uint256 n) internal returns (bool ok, bytes memory data) {
        if (n > 40) revert TooLong(n);
        bytes memory b = new bytes(n + 0);
        if (n > 0) {
            b[0] = bytes1(0xa1);
            b[n - 1] = bytes1(0xb2);
        }
        counter = counter + 1;
        ok = n % 2 == 0;
        // At n = 0 the named result keeps its initial empty buffer.
        if (n > 0) data = b;
    }

    function domainNameAndVersion() internal pure returns (string memory, string memory) {
        return ("Spoke", "1");
    }

    function namedPair(uint256 n) internal pure returns (string memory name, string memory version) {
        name = n % 2 == 0 ? "Short" : "A domain name that is longer than one 32-byte memory word";
        version = "2";
    }

    function twice(uint256 n) internal pure returns (bytes memory, bytes memory) {
        if (n > 40) revert TooLong(n);
        bytes memory b = new bytes(n + 1);
        b[0] = bytes1(0xc3);
        return (b, b);
    }

    function keep(bytes memory x) internal pure returns (bool, bytes memory) {
        return (x.length > 0, x);
    }

    function stamped() internal view returns (uint256, bytes memory) {
        return (counter, abi.encode(counter, lastLen));
    }

    function reassigned() internal pure returns (string memory name, string memory version) {
        (name, version) = domainNameAndVersion();
    }

    function forwarded(uint256 n) internal returns (bool, bytes memory) {
        return sized(n);
    }

    function DOMAIN_SEPARATOR() external pure returns (bytes32) {
        (string memory name, string memory version) = domainNameAndVersion();
        return keccak256(abi.encode(keccak256(bytes(name)), keccak256(bytes(version))));
    }

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 8;
        uint256 n = x / 8;
        if (c == 0) {
            (bool ok, bytes memory data) = sized(n);
            lastOk = ok;
            lastLen = data.length;
            lastHash = keccak256(data);
            otherHash = bytes32(counter);
        }
        if (c == 1) {
            (string memory name, string memory version) = domainNameAndVersion();
            lastLen = bytes(name).length;
            lastHash = keccak256(bytes(name));
            otherHash = keccak256(bytes(version));
        }
        if (c == 2) {
            (string memory name, string memory version) = namedPair(n);
            lastLen = bytes(name).length;
            lastHash = keccak256(bytes(name));
            otherHash = keccak256(bytes(version));
        }
        if (c == 3) {
            (bytes memory first, bytes memory second) = twice(n);
            lastLen = second.length;
            lastHash = keccak256(first);
            otherHash = keccak256(second);
        }
        if (c == 4) {
            if (n > 40) revert TooLong(n);
            bytes memory mine = new bytes(n + 2);
            (bool ok, bytes memory result) = keep(mine);
            mine[0] = bytes1(0xee);
            lastOk = ok;
            lastLen = result.length;
            lastHash = keccak256(result);
        }
        if (c == 5) {
            (uint256 seen, bytes memory snap) = stamped();
            counter = counter + 10;
            lastLen = seen;
            lastHash = keccak256(snap);
            otherHash = bytes32(counter);
        }
        if (c == 6) {
            (string memory name, string memory version) = reassigned();
            lastLen = bytes(version).length;
            lastHash = keccak256(bytes(name));
            otherHash = keccak256(bytes(version));
        }
        if (c == 7) {
            (bool ok, bytes memory data) = forwarded(n);
            lastOk = ok;
            lastLen = data.length;
            lastHash = keccak256(data);
        }
        return c;
    }

    function fail() external pure {
        revert TooLong(0);
    }

    function read() external view returns (uint256, bool, uint256, bytes32, bytes32) {
        return (counter, lastOk, lastLen, lastHash, otherHash);
    }
}
