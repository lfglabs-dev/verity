// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyUintMapSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Storage.lean
 */
contract PropertyUintMapSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("UintMapSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setValue has no unexpected revert
    function testAuto_SetValue_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setValue(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "setValue reverted unexpectedly");
    }
    // Property 2: getValue reads the configured mapping value
    function testAuto_GetValue_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 0), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getValue(uint256)", uint256(1)));
        require(ok, "getValue reverted unexpectedly");
        assertEq(ret.length, 32, "getValue ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getValue should decode the configured mapping value");
    }
}
