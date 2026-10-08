pragma solidity 0.8.34;
struct Box { uint128[] values; uint128 tag; }
contract MultipleDynamicAbi {
    function memoryLeft(Box memory left, Box memory right, uint8 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return left.values[0];
    }
    function memoryRight(Box memory left, Box memory right, uint8 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return right.values[0];
    }
    function calldataLeft(Box calldata left, Box calldata right, uint8 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return left.values[0];
    }
    function calldataRight(Box calldata left, Box calldata right, uint8 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return right.values[0];
    }
}
