// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IPriceOracle {
    function price() external view returns (uint256);
}

contract InterfaceStaticCallFixture {
    uint256 private saved;
    uint256 private observed;

    function read(address oracle) external view returns (uint256) {
        uint256 value = IPriceOracle(oracle).price();
        return value;
    }

    function record(address oracle, uint256 next) external returns (uint256) {
        saved = next;
        uint256 value = IPriceOracle(oracle).price();
        observed = value;
        return value;
    }

    function ping(address oracle, uint256 reject) external returns (uint256) {
        uint256 value;
        saved = reject;
        value = IPriceOracle(oracle).price();
        IPriceOracle(oracle).price();
        if (reject % 2 != 0) revert();
        return value;
    }

    function probe(address oracle, uint256 next) external returns (uint256) {
        saved = next;
        IPriceOracle(oracle).price();
        return next;
    }

    function sum(address first, address second) external view returns (uint256) {
        return quote(first) + quote(second);
    }

    function quote(address oracle) internal view returns (uint256) {
        uint256 value = IPriceOracle(oracle).price();
        return value;
    }

    function stored() external view returns (uint256, uint256) {
        return (saved, observed);
    }
}
