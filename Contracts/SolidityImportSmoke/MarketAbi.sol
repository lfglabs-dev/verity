pragma solidity 0.8.34;
import {Market} from "pinned-midnight/IMidnight.sol";

contract MarketAbi {
    function memoryUnused(Market memory market, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return 7;
    }
    function memoryMaturity(Market memory market, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return market.maturity;
    }
    function memoryTokenLate(Market memory market, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return market.collateralParams[0].token;
    }
    function memoryTokenSecond(Market memory market, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return market.collateralParams[1].token;
    }
    function calldataUnused(Market calldata market, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return 7;
    }
    function calldataMaturity(Market calldata market, uint256 flag) external pure returns (uint256) {
        require(flag != 0, "first");
        return market.maturity;
    }
    function calldataTokenLate(Market calldata market, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return market.collateralParams[0].token;
    }
    function calldataTokenSecond(Market calldata market, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return market.collateralParams[1].token;
    }
    function memoryMidnight(Market memory market, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return market.midnight;
    }
    function calldataMidnight(Market calldata market, uint256 flag) external pure returns (address) {
        require(flag != 0, "first");
        return market.midnight;
    }
}
