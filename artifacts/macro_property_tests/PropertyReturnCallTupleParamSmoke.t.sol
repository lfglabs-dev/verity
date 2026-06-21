// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyReturnCallTupleParamSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/InternalInterfaceSmoke.lean
 */
contract PropertyReturnCallTupleParamSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ReturnCallTupleParamSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `bad` result
    function testTODO_Bad_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bad(address,(uint256,address))", alice, abi.decode(abi.encode(uint256(1), alice), (uint256, address))));
        require(ok, "bad reverted unexpectedly");
        assertEq(ret.length, 32, "bad ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
