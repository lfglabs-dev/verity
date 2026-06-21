// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMappingWordSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Storage.lean
 */
contract PropertyMappingWordSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("MappingWordSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setWord1 has no unexpected revert
    function testAuto_SetWord1_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setWord1(uint256,uint256)", uint256(1), uint256(1)));
        require(ok, "setWord1 reverted unexpectedly");
    }
    // Property 2: getWord1 reads the configured mapping value
    function testAuto_GetWord1_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingWordSlot(bytes32(uint256(uint256(1))), 0, 1), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getWord1(uint256)", uint256(1)));
        require(ok, "getWord1 reverted unexpectedly");
        assertEq(ret.length, 32, "getWord1 ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getWord1 should decode the configured mapping value");
    }
    // Property 3: isWord1NonZero returns true for a non-zero configured mapping word
    function testAuto_IsWord1NonZero_DetectsNonZeroMappingWord() public {
        vm.store(target, _mappingWordSlot(bytes32(uint256(uint256(1))), 0, 1), bytes32(uint256(1)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("isWord1NonZero(uint256)", uint256(1)));
        require(ok, "isWord1NonZero reverted unexpectedly");
        assertEq(ret.length, 32, "isWord1NonZero ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertTrue(actual, "isWord1NonZero should return true when the configured word is non-zero");
    }
}
