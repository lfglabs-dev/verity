pragma solidity 0.8.34;
contract SequenceFixture {
    uint128 stored;
    event Wide(uint256 value, bytes32 tag);
    event Narrow(uint128 indexed first, uint128 second);
    function change(uint128 value) external returns (uint128) {
        stored = value;
        emit Narrow(value, value);
        emit Wide(value, bytes32(uint256(value)));
        return stored;
    }
    function fail() external returns (uint128) {
        stored = 99;
        require(stored == 0, "rollback narrow storage");
        return stored;
    }
    function read() external view returns (uint128) {
        return stored;
    }
}
