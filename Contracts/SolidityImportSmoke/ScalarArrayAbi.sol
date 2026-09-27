pragma solidity 0.8.34;

struct Box { uint128[] values; }

contract ScalarArrayAbi {
    function memoryUnused(Box memory box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return 7;
    }
    function memoryElement(Box memory box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return box.values[0];
    }
    function memorySecond(Box memory box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return box.values[1];
    }
    function calldataUnused(Box calldata box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return 7;
    }
    function calldataElement(Box calldata box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return box.values[0];
    }
    function calldataSecond(Box calldata box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return box.values[1];
    }
}
