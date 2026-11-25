// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// A minimal contract compiled by three pinned solc releases: the default
/// 0.8.34/Osaka profile, the 0.8.35/Amsterdam profile and a 0.8.38/Cancun profile.
contract SolcVersionProbe {
    bytes32 public constant DOMAIN_TYPEHASH =
        keccak256("ProbeDomain(uint256 chainId,address verifyingContract)");

    mapping(address => uint256) public counters;

    function digest(bytes32 tag) public view returns (bytes32) {
        return keccak256(abi.encode(DOMAIN_TYPEHASH, tag, block.chainid, address(this)));
    }

    function bump(uint256 amount) external returns (uint256) {
        counters[msg.sender] += amount;
        return counters[msg.sender];
    }
}
