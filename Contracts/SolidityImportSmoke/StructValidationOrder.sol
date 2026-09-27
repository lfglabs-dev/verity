pragma solidity 0.8.34;
contract StructValidationOrder {
    struct Pair { uint256 pad; uint8 small; }
    function memoryUnused(Pair memory pair) external pure returns (uint256) { return 7; }
    function calldataUnused(Pair calldata pair) external pure returns (uint256) { return 7; }
    function memoryLate(Pair memory pair, uint256 flag) external pure returns (uint8) {
        require(flag != 0, "first");
        return pair.small;
    }
    function calldataLate(Pair calldata pair, uint256 flag) external pure returns (uint8) {
        require(flag != 0, "first");
        return pair.small;
    }
    struct Kinds { bool enabled; address account; uint128 half; }
    function memoryKindsUnused(Kinds memory value) external pure returns (uint256) { return 7; }
    function calldataKindsUnused(Kinds calldata value) external pure returns (uint256) { return 7; }
    function memoryKindsLate(Kinds memory value, uint256 flag) external pure returns (bool, address, uint128) {
        require(flag != 0, "first");
        return (value.enabled, value.account, value.half);
    }
    function calldataKindsLate(Kinds calldata value, uint256 flag) external pure returns (bool, address, uint128) {
        require(flag != 0, "first");
        return (value.enabled, value.account, value.half);
    }
}
