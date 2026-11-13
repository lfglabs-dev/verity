// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// An ERC-7201 namespaced storage struct with members of every placement the importer
/// handles: single- and two-key scalar mappings, `string` members it leaves opaque (never
/// read here), and scalars after them, whose slots must account for the opaque ones.
contract SequenceFixture {
    /// @custom:storage-location erc7201:fixture.storage.Namespaced
    struct NamespacedStorage {
        mapping(address => uint256) balances;
        mapping(address => mapping(address => uint256)) allowances;
        string label;
        uint256 total;
        string symbol;
        uint128 counter;
        bool flag;
    }

    // keccak256(abi.encode(uint256(keccak256("fixture.storage.Namespaced")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant LOCATION = 0x409575e4ba87eaa8eab50489a9b79e7e564512c2701bd2fba5da16348615b500;

    error Insufficient(uint256 available, uint256 requested);

    function _storage() private pure returns (NamespacedStorage storage $) {
        assembly {
            $.slot := LOCATION
        }
    }

    function change(uint256 x) external returns (uint256) {
        NamespacedStorage storage $ = _storage();
        $.balances[msg.sender] += x;
        $.total += x;
        $.counter = uint128(x);
        $.flag = x % 2 == 1;
        return $.total;
    }

    function approve(address spender, uint256 amount) external {
        _storage().allowances[msg.sender][spender] = amount;
    }

    function spend(address owner, uint256 amount) external returns (uint256) {
        NamespacedStorage storage $ = _storage();
        uint256 current = $.allowances[owner][msg.sender];
        require(current >= amount, Insufficient(current, amount));
        $.allowances[owner][msg.sender] = current - amount;
        $.balances[owner] -= amount;
        return current - amount;
    }

    function allowance(address owner, address spender) external view returns (uint256) {
        return _storage().allowances[owner][spender];
    }

    function fail() external view {
        require(_storage().total <= 15, "range");
    }

    function read() external view returns (uint256) {
        NamespacedStorage storage $ = _storage();
        return $.total + $.counter + ($.flag ? 1 : 0);
    }
}
