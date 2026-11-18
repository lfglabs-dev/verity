// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;
pragma experimental ABIEncoderV2;

contract LegacyAbiV2 {
    function scalarAbi(uint8 x, bool flag, address recipient) external pure
        returns (uint256, bool, address)
    {
        return (uint256(x), flag, recipient);
    }
}
