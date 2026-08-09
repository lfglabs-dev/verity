// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyModifiesSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Effects.lean
 */
contract PropertyModifiesSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("ModifiesSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: increment has no unexpected revert
    function testAuto_Increment_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("increment()"));
        require(ok, "increment reverted unexpectedly");
    }
    // Property 2: transferOwnership has no unexpected revert
    function testAuto_TransferOwnership_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("transferOwnership(address)", alice));
        require(ok, "transferOwnership reverted unexpectedly");
    }
    // Property 3: deposit has no unexpected revert
    function testAuto_Deposit_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("deposit(uint256)", uint256(1)));
        require(ok, "deposit reverted unexpectedly");
    }
    // Property 4: getCounter reads storage slot 0 and decodes the result
    function testAuto_GetCounter_ReadsConfiguredStorage() public {
        uint256 expected = uint256(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getCounter()"));
        require(ok, "getCounter reverted unexpectedly");
        assertEq(ret.length, 32, "getCounter ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, expected, "getCounter should return storage slot 0");
    }
}
