// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyCreate2SSTORE2SmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCalls.lean
 */
contract PropertyCreate2SSTORE2SmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("Create2SSTORE2Smoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `deploy` result
    function testTODO_Deploy_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("deploy(uint256,uint256,uint256,uint256)", uint256(1), uint256(1), uint256(1), uint256(1)));
        require(ok, "deploy reverted unexpectedly");
        assertEq(ret.length, 32, "deploy ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: readCode has no unexpected revert
    function testAuto_ReadCode_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("readCode(address,uint256,uint256,uint256)", alice, uint256(1), uint256(1), uint256(1)));
        require(ok, "readCode reverted unexpectedly");
    }
}
