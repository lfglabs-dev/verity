// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyTypedInterfaceCallSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/InternalInterfaceSmoke.lean
 */
contract PropertyTypedInterfaceCallSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("TypedInterfaceCallSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `readBalance` result
    function testTODO_ReadBalance_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readBalance(address,address)", alice, alice));
        require(ok, "readBalance reverted unexpectedly");
        assertEq(ret.length, 32, "readBalance ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `readBalanceViaAlias` result
    function testTODO_ReadBalanceViaAlias_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readBalanceViaAlias(address,address)", alice, alice));
        require(ok, "readBalanceViaAlias reverted unexpectedly");
        assertEq(ret.length, 32, "readBalanceViaAlias ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `transferToken` result
    function testTODO_TransferToken_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("transferToken(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "transferToken reverted unexpectedly");
        assertEq(ret.length, 32, "transferToken ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: transferTokenDiscard has no unexpected revert
    function testAuto_TransferTokenDiscard_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transferTokenDiscard(address,address,uint256)", alice, alice, uint256(1)));
        require(ok, "transferTokenDiscard reverted unexpectedly");
    }
}
