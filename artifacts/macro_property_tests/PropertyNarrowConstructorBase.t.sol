// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyNarrowConstructorBaseTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Helpers.lean
 */
contract PropertyNarrowConstructorBaseTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("NarrowConstructorBase", abi.encode(uint8(27)));
        require(target != address(0), "Deploy failed");
    }

}
