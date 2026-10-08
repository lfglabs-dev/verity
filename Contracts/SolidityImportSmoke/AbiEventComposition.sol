pragma solidity 0.8.34;

struct EventBox { uint128[] values; uint256 tag; }
contract AbiEventComposition {
    uint256 public stored;
    event Decoded(address indexed sender, uint256 indexed tag, uint256 value);

    function memoryChange(EventBox memory box, uint8 flag) external returns (uint256) {
        require(flag != 0, "first");
        uint256 tag = box.tag;
        uint256 value = box.values[0];
        stored = value;
        emit Decoded(msg.sender, tag, value);
        return value;
    }

    function calldataChange(EventBox calldata box, uint8 flag) external returns (uint256) {
        require(flag != 0, "first");
        uint256 tag = box.tag;
        uint256 value = box.values[0];
        stored = value;
        emit Decoded(msg.sender, tag, value);
        return value;
    }

    function failAfterEvent(EventBox memory box) external {
        uint256 tag = box.tag;
        uint256 value = box.values[0];
        stored = value;
        emit Decoded(msg.sender, tag, value);
        require(false, "after");
    }

    function read() external view returns (uint256) { return stored; }
}
