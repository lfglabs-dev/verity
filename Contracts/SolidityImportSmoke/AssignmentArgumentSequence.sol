// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `x++`, `--m[k]` and `x = v` as arguments of internal calls, `abi.encode` and a hashed
// `abi.encode` nested in `abi.encodePacked` (the EIP-2612 `permit` / Safe nonce shape).
// Both solc pipelines evaluate the arguments left to right, each write at its own
// position, so siblings before it read the old value and siblings after it the new one.
contract SequenceFixture {
    enum Kind { Plain, Tagged, Sealed }

    bytes32 internal constant TYPEHASH = keccak256("Use(address owner,uint256 value,uint256 nonce)");

    uint256 internal saved;
    uint256 internal counter;
    mapping(uint256 => uint256) internal slots;
    mapping(address => uint256) internal nonces;
    mapping(uint256 => mapping(uint256 => uint256)) internal grid;

    function _mix(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
        return uint256(keccak256(abi.encode(a, b, c)));
    }

    function _tag(Kind kind, uint256 a, uint256 b) internal pure returns (uint256) {
        return uint256(kind) * 1e9 + a * 1e3 + b;
    }

    function _domain() internal view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, address(this), counter));
    }

    function change(uint256 next) external returns (uint256) {
        uint256 k = next % 3;
        uint256 r;
        if (next % 6 == 0) {
            // Post-increment of a state variable, read before and after, in a call and an encoding.
            r = _mix(counter, counter++, counter);
            r ^= uint256(keccak256(abi.encode(counter, counter++, counter)));
        } else if (next % 6 == 1) {
            // Decrement of a mapping element: panics at zero, after the division on its left.
            r = _mix(10 / (next % 7), slots[k]--, slots[k]);
            r ^= uint256(keccak256(abi.encode(slots[k], --slots[k], 10 / (next % 5))));
        } else if (next % 6 == 2) {
            // EIP-2612 shape: the nonce use inside a hashed `abi.encode` nested in `encodePacked`,
            // after a view helper that reads the incremented variable.
            unchecked {
                r = uint256(keccak256(abi.encodePacked(
                    "\x19\x01",
                    _domain(),
                    keccak256(abi.encode(TYPEHASH, msg.sender, next, counter--, nonces[msg.sender]++)),
                    counter)));
            }
        } else if (next % 6 == 3) {
            // A local update and a storage assignment expression.
            uint256 x = next % 11;
            r = _mix(x, x++, x);
            r ^= _mix(counter, counter = next % 100, counter);
            r ^= uint256(keccak256(abi.encode(counter, counter = x, counter)));
            r ^= _tag(Kind(next % 3), counter--, counter);
        } else if (next % 6 == 4) {
            // Pre-increment and two updates of the same element in one argument list.
            r = _mix(++slots[k], slots[k], slots[k]++);
            r ^= uint256(keccak256(abi.encode(slots[k]++, ++slots[k], slots[k])));
        } else {
            // A nested mapping element beside a second update.
            r = _mix(grid[k][k], grid[k][k]++, grid[k][k]);
            r ^= uint256(keccak256(abi.encode(grid[k][k], ++grid[k][k], counter++, counter)));
        }
        saved = uint256(keccak256(abi.encode(saved, r)));
        return saved ^ counter ^ slots[k] ^ nonces[msg.sender];
    }

    function fail() external {
        saved = 77;
        revert();
    }

    function read() external view returns (uint256) {
        return saved ^ counter ^ slots[0] ^ slots[1] ^ slots[2] ^ nonces[address(this)] ^ grid[0][0];
    }
}
