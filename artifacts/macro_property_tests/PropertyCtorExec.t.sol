// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyCtorExecTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ConstructorExecutable.lean
 */
contract PropertyCtorExecTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("CtorExec", abi.encode(uint256(1)));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: minterOf reads storage slot 5 and decodes the result
    function testAuto_MinterOf_ReadsConfiguredStorage() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(5)), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("minterOf()"));
        require(ok, "minterOf reverted unexpectedly");
        assertEq(ret.length, 32, "minterOf ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "minterOf should return storage slot 5");
    }
}
