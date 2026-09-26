pragma solidity 0.8.34;

library Notices {
    event Changed(address indexed sender, uint256 value, bool indexed accepted, bytes32 indexed tag);
}

contract SequenceFixture {
    uint256 stored;
    event Detail(uint256 indexed low, uint256 middle, uint256 full, address owner, bool accepted, bytes32 tag);
    event Empty();

    function change(uint256 value) external returns (uint256) {
        uint256 old = stored;
        stored = value;
        uint128 narrow = uint128(value);
        uint8 low = uint8(value);
        uint16 middle = uint16(value);
        bytes32 tag = bytes32(value);
        bool accepted = value > 1;
        emit Notices.Changed(msg.sender, narrow, accepted, tag);
        emit Detail(low, middle, value, address(this), accepted, bytes32(value));
        emit Empty();
        return old;
    }

    function fail() external returns (uint256) {
        stored = 99;
        emit Notices.Changed(msg.sender, 99, false, bytes32(uint256(99)));
        emit Empty();
        require(stored == 0, "rollback emitted events");
        return stored;
    }

    function read() external returns (uint256) {
        emit Empty();
        emit Empty();
        return stored;
    }
}
