// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// The contract-typed `this` used as a value. solc represents a contract-typed value by its
// address word, so each root must agree with its `address(this)` twin on every route.
contract ThisValueFixture {
    bytes32 internal constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)");

    event Seen(ThisValueFixture indexed self, ThisValueFixture other, uint256 tag);

    ThisValueFixture private stored;

    // EIP-712 domain separator with `verifyingContract` written as `this`.
    function domainSeparator() external view returns (bytes32) {
        return keccak256(abi.encode(DOMAIN_TYPEHASH, block.chainid, this));
    }

    function domainSeparatorAddress() external view returns (bytes32) {
        return keccak256(abi.encode(DOMAIN_TYPEHASH, block.chainid, address(this)));
    }

    // Packed encoding: a contract-typed value is 20 bytes, like an address.
    function packed(uint256 tag) external view returns (bytes32) {
        return keccak256(abi.encodePacked(uint8(tag), this, tag));
    }

    function packedAddress(uint256 tag) external view returns (bytes32) {
        return keccak256(abi.encodePacked(uint8(tag), address(this), tag));
    }

    function encoded(uint256 tag) external view returns (bytes memory) {
        return abi.encode(tag, this);
    }

    // Comparisons with a contract-typed value converted from an address.
    function isSelf(address account) external view returns (bool) {
        return this == ThisValueFixture(account);
    }

    function isOther(address account) external view returns (bool) {
        return ThisValueFixture(account) != this;
    }

    // `this` passed to an internal function parameter, bound to a local and returned.
    function viaArgument(uint256 tag) external view returns (address) {
        return pick(this, tag);
    }

    function viaLocal() external view returns (address) {
        ThisValueFixture self = this;
        return address(self);
    }

    function self() external view returns (ThisValueFixture) {
        return this;
    }

    // `this` as an event argument, indexed and not, and as a stored value.
    function announce(uint256 tag) external {
        emit Seen(this, this, tag);
    }

    function remember() external {
        stored = this;
    }

    function recalled() external view returns (address) {
        return address(stored);
    }

    function pick(ThisValueFixture target, uint256 tag) internal pure returns (address) {
        return tag % 2 == 0 ? address(target) : address(0);
    }
}
