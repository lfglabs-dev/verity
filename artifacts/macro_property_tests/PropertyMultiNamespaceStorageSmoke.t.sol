// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMultiNamespaceStorageSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Namespaces.lean
 */
contract PropertyMultiNamespaceStorageSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("MultiNamespaceStorageSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: writeState has no unexpected revert
    function testAuto_WriteState_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("writeState(uint256,address)", uint256(1), alice));
        require(ok, "writeState reverted unexpectedly");
    }
    // Property 2: readStateRoot reads storage slot 0 and decodes the result
    function testAuto_ReadStateRoot_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readStateRoot()"));
        require(ok, "readStateRoot reverted unexpectedly");
        assertEq(ret.length, 32, "readStateRoot ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "readStateRoot should return storage slot 0");
    }
    // Property 3: readRelayer reads the configured mapping value
    function testAuto_ReadRelayer_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readRelayer(address)", alice));
        require(ok, "readRelayer reverted unexpectedly");
        assertEq(ret.length, 32, "readRelayer ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "readRelayer should decode the configured mapping value");
    }
}
