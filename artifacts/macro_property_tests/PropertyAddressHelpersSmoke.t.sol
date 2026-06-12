// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyAddressHelpersSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyAddressHelpersSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("AddressHelpersSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setDelegate has no unexpected revert
    function testAuto_SetDelegate_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setDelegate(address,address)", alice, alice));
        require(ok, "setDelegate reverted unexpectedly");
    }
    // Property 2: getDelegate reads the configured mapping value
    function testAuto_GetDelegate_ReadsConfiguredMapping() public {
        address expected = alice;
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getDelegate(address)", alice));
        require(ok, "getDelegate reverted unexpectedly");
        assertEq(ret.length, 32, "getDelegate ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "getDelegate should decode the configured mapping value");
    }
    // Property 3: clearDelegate has no unexpected revert
    function testAuto_ClearDelegate_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("clearDelegate(address)", alice));
        require(ok, "clearDelegate reverted unexpectedly");
    }
    // Property 4: hasDelegate returns true for a non-zero configured mapping address
    function testAuto_HasDelegate_DetectsNonZeroMappingAddress() public {
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(uint160(address(0xBEEF)))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("hasDelegate(address)", alice));
        require(ok, "hasDelegate reverted unexpectedly");
        assertEq(ret.length, 32, "hasDelegate ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertTrue(actual, "hasDelegate should return true when the configured address is non-zero");
    }
    // Property 5: isDelegateZero returns true for a zero configured mapping address
    function testAuto_IsDelegateZero_DetectsZeroMappingAddress() public {
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(0));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("isDelegateZero(address)", alice));
        require(ok, "isDelegateZero reverted unexpectedly");
        assertEq(ret.length, 32, "isDelegateZero ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertTrue(actual, "isDelegateZero should return true when the configured address is zero");
    }
    // Property 6: setOwnerForId has no unexpected revert
    function testAuto_SetOwnerForId_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setOwnerForId(uint256,address)", uint256(1), alice));
        require(ok, "setOwnerForId reverted unexpectedly");
    }
    // Property 7: getOwnerForId reads the configured mapping value
    function testAuto_GetOwnerForId_ReadsConfiguredMapping() public {
        address expected = alice;
        vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 1), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getOwnerForId(uint256)", uint256(1)));
        require(ok, "getOwnerForId reverted unexpectedly");
        assertEq(ret.length, 32, "getOwnerForId ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "getOwnerForId should decode the configured mapping value");
    }
}
