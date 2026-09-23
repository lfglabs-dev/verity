// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyGetterCallerTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/LinkedGettersAndDeferred.lean
 */
contract PropertyGetterCallerTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("GetterCaller");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `readManager` result
    function testTODO_ReadManager_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readManager(address)", alice));
        require(ok, "readManager reverted unexpectedly");
        assertEq(ret.length, 32, "readManager ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: TODO decode and assert `readTotal` result
    function testTODO_ReadTotal_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readTotal(address)", alice));
        require(ok, "readTotal reverted unexpectedly");
        assertEq(ret.length, 32, "readTotal ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 3: TODO decode and assert `readFlag` result
    function testTODO_ReadFlag_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readFlag(address)", alice));
        require(ok, "readFlag reverted unexpectedly");
        assertEq(ret.length, 32, "readFlag ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `readBalance` result
    function testTODO_ReadBalance_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readBalance(address,address)", alice, alice));
        require(ok, "readBalance reverted unexpectedly");
        assertEq(ret.length, 32, "readBalance ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `readId` result
    function testTODO_ReadId_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readId(address,uint256)", alice, uint256(1)));
        require(ok, "readId reverted unexpectedly");
        assertEq(ret.length, 32, "readId ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 6: TODO decode and assert `readAllowance` result
    function testTODO_ReadAllowance_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("readAllowance(address,address,address)", alice, alice, alice));
        require(ok, "readAllowance reverted unexpectedly");
        assertEq(ret.length, 32, "readAllowance ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
