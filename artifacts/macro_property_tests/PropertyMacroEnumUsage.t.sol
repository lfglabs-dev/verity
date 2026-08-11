// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMacroEnumUsageTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/EnumFeatureTest.lean
 */
contract PropertyMacroEnumUsageTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("MacroEnumUsage");
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
    // Property 2: TODO decode and assert `active` result
    function testTODO_Active_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("active()"));
        require(ok, "active reverted unexpectedly");
        assertEq(ret.length, 32, "active ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `castStatus` result
    function testTODO_CastStatus_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("castStatus(uint256)", uint256(1)));
        require(ok, "castStatus reverted unexpectedly");
        assertEq(ret.length, 32, "castStatus ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: setStatus has no unexpected revert
    function testAuto_SetStatus_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setStatus(uint8)", uint8(0)));
        require(ok, "setStatus reverted unexpectedly");
    }
    // Property 5: announceStatus has no unexpected revert
    function testAuto_AnnounceStatus_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("announceStatus(uint8)", uint8(0)));
        require(ok, "announceStatus reverted unexpectedly");
    }
    // Property 6: getStatus reads storage slot 0 and decodes the result
    function testAuto_GetStatus_ReadsConfiguredStorage() public {
        uint8 expected = uint8(0);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getStatus()"));
        require(ok, "getStatus reverted unexpectedly");
        assertEq(ret.length, 32, "getStatus ABI return length mismatch (expected 32 bytes)");
        uint8 actual = abi.decode(ret, (uint8));
        assertEq(actual, expected, "getStatus should return storage slot 0");
    }
    // Property 7: setStatusAt has no unexpected revert
    function testAuto_SetStatusAt_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setStatusAt(uint256,uint8)", uint256(1), uint8(0)));
        require(ok, "setStatusAt reverted unexpectedly");
    }
    // Property 8: getStatusAt reads the configured mapping value
    function testAuto_GetStatusAt_ReadsConfiguredMapping() public {
        uint8 expected = uint8(0);
        vm.store(target, _mappingSlot(bytes32(uint256(uint256(1))), 1), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getStatusAt(uint256)", uint256(1)));
        require(ok, "getStatusAt reverted unexpectedly");
        assertEq(ret.length, 32, "getStatusAt ABI return length mismatch (expected 32 bytes)");
        uint8 actual = abi.decode(ret, (uint8));
        assertEq(actual, expected, "getStatusAt should decode the configured mapping value");
    }
}
