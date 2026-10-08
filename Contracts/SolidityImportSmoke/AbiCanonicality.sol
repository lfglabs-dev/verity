pragma solidity 0.8.34;
contract AbiCanonicality {
    function byteValue(uint8 value) external pure returns (uint8) { return value; }
    function addressValue(address value) external pure returns (address) { return value; }
    function boolValue(bool value) external pure returns (bool) { return value; }
    function shortValue(uint16 value) external pure returns (uint16) { return value; }
    function halfValue(uint128 value) external pure returns (uint128) { return value; }
    function wideValue(uint248 value) external pure returns (uint248) { return value; }
    function fullValue(uint256 value) external pure returns (uint256) { return value; }
    function unusedValue(uint8 value) external pure returns (uint256) { return 7; }
    function mixedValue(uint256 full, uint8 narrow, address account, bool flag)
        external pure returns (uint256, uint8, address, bool) {
        return (full, narrow, account, flag);
    }
    struct Pair { uint256 first; uint256 second; }
    function structValue(Pair calldata pair, uint8 narrow)
        external pure returns (uint256, uint256, uint8) {
        return (pair.first, pair.second, narrow);
    }
}
