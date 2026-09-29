// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyG26ATest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HopContextAndMutableTuples.lean
 */
contract PropertyG26ATest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("G26A");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `preview` result
    function testTODO_Preview_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("preview(address,uint256)", alice, uint256(1)));
        require(ok, "preview reverted unexpectedly");
        require(ret.length >= 64, "preview ABI tuple return payload unexpectedly short");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `previewOne` result
    function testTODO_PreviewOne_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("previewOne(address)", alice));
        require(ok, "previewOne reverted unexpectedly");
        assertEq(ret.length, 32, "previewOne ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: readK reads storage slot 0 and decodes the result
    function testAuto_ReadK_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readK()"));
        require(ok, "readK reverted unexpectedly");
        assertEq(ret.length, 32, "readK ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "readK should return storage slot 0");
    }
}
