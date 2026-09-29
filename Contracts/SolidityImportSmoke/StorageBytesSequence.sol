pragma solidity 0.8.34;
contract SequenceFixture {
    bytes32 stored;
    function change(uint256 value) external returns (bytes32) {
        stored = bytes32(value);
        return stored;
    }
    function fail() external returns (bytes32) {
        stored = bytes32(uint256(99));
        require(stored == bytes32(uint256(0)), "rollback bytes write");
        return stored;
    }
    function read() external returns (bytes32) {
        bytes32 old = stored;
        delete stored;
        return old;
    }
}
