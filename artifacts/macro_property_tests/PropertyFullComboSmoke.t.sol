// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyFullComboSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/SecurityCombos.lean
 */
contract PropertyFullComboSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("FullComboSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: getBalance reads storage slot 1 and decodes the result
    function testAuto_GetBalance_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(1)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getBalance()"));
        require(ok, "getBalance reverted unexpectedly");
        assertEq(ret.length, 32, "getBalance ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getBalance should return storage slot 1");
    }
}
