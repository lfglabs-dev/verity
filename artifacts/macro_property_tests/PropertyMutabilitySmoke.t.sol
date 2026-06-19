// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyMutabilitySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Declarations.lean
 */
contract PropertyMutabilitySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("MutabilitySmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: deposit returns the active call value
    function testAuto_Deposit_ReturnsMsgValue() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("deposit()"));
        require(ok, "deposit reverted unexpectedly");
        assertEq(ret.length, 32, "deposit ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 0, "deposit should preserve the expected value");
    }
    // Property 2: currentOwner reads storage slot 0 and decodes the result
    function testAuto_CurrentOwner_ReadsConfiguredStorage() public {
        address expected = alice;
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(uint160(expected))));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("currentOwner()"));
        require(ok, "currentOwner reverted unexpectedly");
        assertEq(ret.length, 32, "currentOwner ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, expected, "currentOwner should return storage slot 0");
    }
    // Property 3: double returns the declared constant result
    function testAuto_Double_ReturnsDeclaredConstant() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("double(uint256)", uint256(1)));
        require(ok, "double reverted unexpectedly");
        assertEq(ret.length, 32, "double ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, 2, "double should return the declared constant");
    }
}
