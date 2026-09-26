pragma solidity 0.8.34;

contract SequenceFixture {
    mapping(address => uint128) balances;
    mapping(address => mapping(address => bool)) authorized;
    mapping(address => mapping(bytes32 => uint128)) consumed;
    mapping(uint256 => bytes32) words;

    function change(uint256 value) external returns (uint128, bool, uint128, bytes32) {
        balances[msg.sender] = uint128(value);
        authorized[msg.sender][address(this)] = true;
        consumed[msg.sender][bytes32(value)] = uint128(value);
        words[value] = bytes32(value);
        return (balances[msg.sender], authorized[msg.sender][address(this)],
            consumed[msg.sender][bytes32(value)], words[value]);
    }

    function fail() external returns (uint128) {
        balances[msg.sender] = 99;
        authorized[msg.sender][address(this)] = false;
        consumed[msg.sender][bytes32(uint256(7))] = 99;
        require(balances[msg.sender] < 1, "rollback mapping writes");
        return balances[msg.sender];
    }

    function read() external returns (uint128, bool, uint128, bytes32) {
        delete balances[msg.sender];
        delete authorized[msg.sender][address(this)];
        delete consumed[msg.sender][bytes32(uint256(7))];
        delete words[7];
        return (balances[msg.sender], authorized[msg.sender][address(this)],
            consumed[msg.sender][bytes32(uint256(7))], words[7]);
    }
}
