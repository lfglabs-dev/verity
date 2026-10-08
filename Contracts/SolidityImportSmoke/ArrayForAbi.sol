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
    function memoryLength(Box memory box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        uint256 total;
        for (uint256 index = 0; index < box.values.length; index++) {
            total = total + 1;
        }
        return total;
    }
    function calldataLength(Box calldata box, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        uint256 total;
        for (uint256 index = 0; index < box.values.length; index++) {
            total = total + 1;
        }
        return total;
    }
}
