// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library LegacySignedConstant {
    uint256 internal constant VALUE = uint256(int8(200));
    uint256 internal constant ALIAS = VALUE;
}

contract LegacyDirectImmutable {
    uint256 internal immutable I = uint256(int8(200));

    function readI() external view returns (uint256) {
        return I;
    }
}

contract LegacyConstantImmutable {
    uint256 internal immutable I = LegacySignedConstant.ALIAS;

    function readI() external view returns (uint256) {
        return I;
    }
}

contract LegacySupportedImmutable {
    uint256 internal immutable I = uint256(uint8(42));

    function readI() external view returns (uint256) {
        return I;
    }
}
