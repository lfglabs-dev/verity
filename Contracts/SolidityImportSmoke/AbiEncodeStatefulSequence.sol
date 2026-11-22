// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type Nonce is uint256;

// State-changing internal helpers as `abi.encode` arguments (the OpenZeppelin
// `ERC20Permit` / `Governor` nonce shape). Both solc pipelines evaluate the
// arguments left to right before encoding, so each helper runs once, in order,
// and a plain storage read between two helpers sees the earlier write only.
contract SequenceFixture {
    bytes32 internal constant PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    uint256 internal saved;
    uint256 internal counter;
    mapping(address => uint256) internal nonces;

    function _bump(uint256 k) internal returns (uint256) {
        counter = (counter * 10 + k) % 1000003;
        return counter;
    }

    function _useNonce(address owner) internal returns (uint256) {
        unchecked {
            return nonces[owner]++;
        }
    }

    function _useWrapped(address owner) internal returns (Nonce) {
        return Nonce.wrap(nonces[owner]++);
    }

    function change(uint256 next) external returns (uint256) {
        bytes32 digest;
        if (next % 4 == 0) {
            // Two helpers with storage reads before, between and after them.
            digest = keccak256(abi.encode(counter, _bump(next % 7 + 1), counter, _bump(3), counter));
        } else if (next % 4 == 1) {
            // ERC20Permit: two nonce uses in one encoding, so their order is visible.
            digest = keccak256(abi.encode(
                PERMIT_TYPEHASH, msg.sender, address(this), next,
                _useNonce(msg.sender), _useNonce(msg.sender), next >> 2));
        } else if (next % 4 == 2) {
            // Narrowing conversion and `unwrap` over helpers; a nested hashed encoding.
            digest = keccak256(abi.encode(
                uint8(_bump(next % 5)),
                Nonce.unwrap(_useWrapped(msg.sender)),
                keccak256(abi.encode(_bump(9), counter)),
                counter));
        } else {
            bytes memory encoded = abi.encode(_useNonce(address(this)), counter, _bump(next % 3));
            digest = keccak256(encoded) ^ bytes32(encoded.length);
        }
        saved = uint256(digest);
        return saved ^ counter ^ nonces[msg.sender];
    }

    function fail() external {
        saved = 77;
        revert();
    }

    function read() external view returns (uint256) {
        return saved ^ counter ^ nonces[address(this)];
    }
}
