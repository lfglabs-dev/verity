// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Two-level nested mapping members of storage structs reached through a state variable, a
// 1-key and a 2-key mapping: writes, reads, checked compound assignment on a packed leaf and
// `delete`, at keccak256(k2 . keccak256(k1 . memberSlot)).
contract SequenceFixture {
    struct Account {
        uint64 nonce;
        mapping(address => mapping(uint256 => uint256)) allowance;
        mapping(uint256 => mapping(address => bool)) approved;
        mapping(bytes32 => mapping(uint8 => uint32)) packed;
        uint128 balance;
    }

    uint256 private total;
    Account private single;
    mapping(address => Account) private accounts;
    mapping(bytes32 => mapping(address => Account)) private pairs;

    function change(uint256 x) external returns (uint256) {
        address who = address(uint160(x % 4));
        address spender = address(uint160((x >> 2) % 4));
        uint256 id = (x >> 4) % 3;
        accounts[who].allowance[spender][id] = x;
        single.allowance[spender][id] += 1;
        pairs[bytes32(id)][who].allowance[spender][id] = x >> 1;
        accounts[who].approved[id][spender] = x % 3 == 0;
        accounts[who].packed[bytes32(x % 5)][uint8(id)] += uint32(x % 100);
        accounts[who].nonce += 1;
        if (x % 7 == 6) delete accounts[who].allowance[spender][id];
        total = total + accounts[who].allowance[spender][id] % 1000 +
            single.allowance[spender][id] + pairs[bytes32(id)][who].allowance[spender][id] % 100 +
            (accounts[who].approved[id][spender] ? 1 : 0) +
            accounts[who].packed[bytes32(x % 5)][uint8(id)] + accounts[who].nonce;
        return total;
    }

    // The stateful harness's reverting call: its write is rolled back.
    function fail() external {
        total = total + 1;
        revert();
    }

    function read() external view returns (uint256) {
        return total;
    }
}
