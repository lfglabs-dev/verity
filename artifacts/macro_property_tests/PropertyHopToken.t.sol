// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyHopTokenTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Erc20BalanceHop.lean
 */
contract PropertyHopTokenTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("HopToken");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: balanceOf reads the configured mapping value
    function testAuto_BalanceOf_ReadsConfiguredMapping() public {
        uint256 expected = uint256(1);
        vm.store(target, _mappingSlot(bytes32(uint256(uint160(alice))), 0), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("balanceOf(address)", alice));
        require(ok, "balanceOf reverted unexpectedly");
        assertEq(ret.length, 32, "balanceOf ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "balanceOf should decode the configured mapping value");
    }
    // Property 2: TODO decode and assert `transfer` result
    function testTODO_Transfer_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("transfer(address,uint256)", alice, uint256(1)));
        require(ok, "transfer reverted unexpectedly");
        assertEq(ret.length, 32, "transfer ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
