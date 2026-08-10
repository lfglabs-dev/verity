// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyPackedStorageLoweringSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Storage.lean
 */
contract PropertyPackedStorageLoweringSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("PackedStorageLoweringSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setFlags has no unexpected revert
    function testAuto_SetFlags_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setFlags(uint256)", uint256(1)));
        require(ok, "setFlags reverted unexpectedly");
    }
    // Property 2: setEpoch has no unexpected revert
    function testAuto_SetEpoch_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setEpoch(uint256)", uint256(1)));
        require(ok, "setEpoch reverted unexpectedly");
    }
    // Property 3: setAmount has no unexpected revert
    function testAuto_SetAmount_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setAmount(uint128)", uint128(1)));
        require(ok, "setAmount reverted unexpectedly");
    }
    // Property 4: rewriteAmount has no unexpected revert
    function testAuto_RewriteAmount_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("rewriteAmount()"));
        require(ok, "rewriteAmount reverted unexpectedly");
    }
    // Property 5: incrementAmount has no unexpected revert
    function testAuto_IncrementAmount_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("incrementAmount(uint128)", uint128(1)));
        require(ok, "incrementAmount reverted unexpectedly");
    }
    // Property 6: getFlags reads storage slot 0 and decodes the result
    function testAuto_GetFlags_ReadsConfiguredStorage() public {
        uint16 expected = uint16(1);
        vm.store(target, bytes32(uint256(0)), bytes32(uint256(expected)));
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("getFlags()"));
        require(ok, "getFlags reverted unexpectedly");
        assertEq(ret.length, 32, "getFlags ABI return length mismatch (expected 32 bytes)");
        uint16 actual = abi.decode(ret, (uint16));
        assertEq(actual, expected, "getFlags should return storage slot 0");
    }
    // Property 7: TODO decode and assert `collateralAt` result
    function testTODO_CollateralAt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("collateralAt(uint256)", uint256(1)));
        require(ok, "collateralAt reverted unexpectedly");
        assertEq(ret.length, 32, "collateralAt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 8: setCollateralAt has no unexpected revert
    function testAuto_SetCollateralAt_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setCollateralAt(uint256,uint128)", uint256(1), uint128(1)));
        require(ok, "setCollateralAt reverted unexpectedly");
    }
    // Property 9: setAmountFromCollateral has no unexpected revert
    function testAuto_SetAmountFromCollateral_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setAmountFromCollateral()"));
        require(ok, "setAmountFromCollateral reverted unexpectedly");
    }
}
