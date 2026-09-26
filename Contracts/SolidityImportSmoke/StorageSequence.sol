pragma solidity 0.8.34;

// The three names match the sequence instrument's call interface. `read` also
// deletes fields deliberately, so subsequent calls exercise persistent state.
contract SequenceFixture {
    uint128 low;
    uint128 high;
    address owner;
    uint96 tag;
    uint256 stored;

    function change(uint256 value) external returns (uint128, uint128, address, uint96, uint256) {
        low = uint128(value);
        high = uint128(value / 2);
        owner = msg.sender;
        tag = uint96(value);
        stored = value;
        return (low, high, owner, tag, stored);
    }

    function fail() external returns (uint256) {
        low = 123;
        stored = 99;
        require(stored < 1, "rollback writes");
        return stored;
    }

    function read() external returns (uint128, uint128, address, uint96, uint256) {
        delete low;
        delete stored;
        return (low, high, owner, tag, stored);
    }
}
