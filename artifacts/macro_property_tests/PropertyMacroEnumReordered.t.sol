// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMacroEnumReorderedTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/EnumFeatureTest.lean
 */
contract PropertyMacroEnumReorderedTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("MacroEnumReordered");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: identity returns the direct parameter value
    function testAuto_Identity_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("identity(uint8)", uint8(0)));
        require(ok, "identity reverted unexpectedly");
        assertEq(ret.length, 32, "identity ABI return length mismatch (expected 32 bytes)");
        uint8 actual = abi.decode(ret, (uint8));
        assertEq(actual, uint8(0), "identity should preserve the expected value");
    }
}
