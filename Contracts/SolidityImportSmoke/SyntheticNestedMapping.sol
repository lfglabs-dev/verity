// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Two-level nested mappings `mapping(K1 => mapping(K2 => V))` as members of storage structs
// reached through a state variable, a 1-key or a 2-key mapping: the leaf of `s.m[k1][k2]` is
// keccak256(k2 . keccak256(k1 . memberSlot)), with `memberSlot` solc's layout slot of the member
// (SyntheticNestedMappingChecks.lean).
contract SyntheticNestedMapping {
    struct Account {
        uint64 nonce;
        mapping(address => mapping(uint256 => uint256)) allowance;
        mapping(uint256 => mapping(address => bool)) approved;
        mapping(bytes32 => mapping(uint8 => uint32)) packed;
        uint128 balance;
    }

    Account private single;
    mapping(address => Account) private accounts;
    mapping(bytes32 => mapping(address => Account)) private pairs;

    function setAllowance(address owner, address spender, uint256 id, uint256 v) external {
        accounts[owner].allowance[spender][id] = v;
        single.allowance[spender][id] = v + 1;
        pairs[bytes32(id)][owner].allowance[spender][id] = v + 2;
        accounts[owner].nonce += 1;
    }

    function allowanceOf(address owner, address spender, uint256 id)
        external
        view
        returns (uint256, uint256, uint256, uint64)
    {
        return (
            accounts[owner].allowance[spender][id],
            single.allowance[spender][id],
            pairs[bytes32(id)][owner].allowance[spender][id],
            accounts[owner].nonce
        );
    }

    function approve(address owner, uint256 id, address operator, bool on) external {
        accounts[owner].approved[id][operator] = on;
    }

    function isApproved(address owner, uint256 id, address operator) external view returns (bool) {
        return accounts[owner].approved[id][operator];
    }

    function bumpPacked(address owner, bytes32 key, uint8 lane, uint32 by) external returns (uint32) {
        accounts[owner].packed[key][lane] += by;
        return accounts[owner].packed[key][lane];
    }

    function clearAllowance(address owner, address spender, uint256 id) external {
        delete accounts[owner].allowance[spender][id];
    }
}

// Shapes outside the slice fail closed; an inner mapping passed as a storage argument imports.
contract SyntheticNestedMappingUnsupported {
    enum Kind { A, B }

    struct Deep {
        mapping(address => mapping(uint256 => mapping(uint256 => uint256))) deep;
        mapping(address => mapping(Kind => uint256)) byKind;
        mapping(address => mapping(uint256 => uint256)) plain;
    }

    mapping(address => Deep) private deeps;

    function readDeep(address a, uint256 i, uint256 j) external view returns (uint256) {
        return deeps[a].deep[a][i][j];
    }

    function readByKind(address a) external view returns (uint256) {
        return deeps[a].byKind[a][Kind.B];
    }

    function _sum(mapping(uint256 => uint256) storage m) private view returns (uint256) {
        return m[0] + m[1];
    }

    function passInner(address a) external view returns (uint256) {
        return _sum(deeps[a].plain[a]);
    }
}
