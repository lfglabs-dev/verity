pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 stored;

    function change(uint256 value) external {
        stored = value;
    }

    function fail() external {
        stored = 99;
        require(stored < 1, "rollback void write");
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
