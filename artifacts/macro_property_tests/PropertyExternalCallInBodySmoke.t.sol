// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyExternalCallInBodySmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCallInBodySmoke.lean
 */
contract PropertyExternalCallInBodySmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ExternalCallInBodySmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: TODO decode and assert `linkedRead` result
    function testTODO_LinkedRead_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("linkedRead()"));
        require(ok, "linkedRead reverted unexpectedly");
        assertEq(ret.length, 32, "linkedRead ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 2: linkedWrite has no unexpected revert
    function testAuto_LinkedWrite_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("linkedWrite(uint256,bytes)", uint256(1), hex"CAFE"));
        require(ok, "linkedWrite reverted unexpectedly");
    }
    // Property 3: TODO decode and assert `pureNarrow` result
    function testTODO_PureNarrow_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pureNarrow()"));
        require(ok, "pureNarrow reverted unexpectedly");
        assertEq(ret.length, 32, "pureNarrow ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 4: TODO decode and assert `pureDirtyUint` result
    function testTODO_PureDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pureDirtyUint()"));
        require(ok, "pureDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "pureDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 5: TODO decode and assert `directDirtyUint` result
    function testTODO_DirectDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("directDirtyUint()"));
        require(ok, "directDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "directDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 6: TODO decode and assert `nestedDirtyUint` result
    function testTODO_NestedDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("nestedDirtyUint()"));
        require(ok, "nestedDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "nestedDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 7: TODO decode and assert `nestedExternalArg` result
    function testTODO_NestedExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("nestedExternalArg()"));
        require(ok, "nestedExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "nestedExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 8: TODO decode and assert `bindDirtyUint` result
    function testTODO_BindDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bindDirtyUint()"));
        require(ok, "bindDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "bindDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 9: TODO decode and assert `tryDirtyUint` result
    function testTODO_TryDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("tryDirtyUint()"));
        require(ok, "tryDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "tryDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 10: TODO decode and assert `callResultDirtyUint` result
    function testTODO_CallResultDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("callResultDirtyUint()"));
        require(ok, "callResultDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "callResultDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 11: TODO decode and assert `tryNotifyBool` result
    function testTODO_TryNotifyBool_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("tryNotifyBool(bool)", true));
        require(ok, "tryNotifyBool reverted unexpectedly");
        assertEq(ret.length, 32, "tryNotifyBool ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 12: TODO decode and assert `tryDirtyPair` result
    function testTODO_TryDirtyPair_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("tryDirtyPair()"));
        require(ok, "tryDirtyPair reverted unexpectedly");
        assertEq(ret.length, 32, "tryDirtyPair ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 13: TODO decode and assert `safeBindDirtyUint` result
    function testTODO_SafeBindDirtyUint_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("safeBindDirtyUint()"));
        require(ok, "safeBindDirtyUint reverted unexpectedly");
        assertEq(ret.length, 32, "safeBindDirtyUint ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 14: TODO decode and assert `leanHelperNestedExternal` result
    function testTODO_LeanHelperNestedExternal_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("leanHelperNestedExternal()"));
        require(ok, "leanHelperNestedExternal reverted unexpectedly");
        assertEq(ret.length, 32, "leanHelperNestedExternal ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 15: TODO decode and assert `bindNestedExternalArg` result
    function testTODO_BindNestedExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bindNestedExternalArg()"));
        require(ok, "bindNestedExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "bindNestedExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 16: statementNestedExternalArg has no unexpected revert
    function testAuto_StatementNestedExternalArg_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("statementNestedExternalArg()"));
        require(ok, "statementNestedExternalArg reverted unexpectedly");
    }
    // Property 17: legacyNarrowArgs has no unexpected revert
    function testAuto_LegacyNarrowArgs_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("legacyNarrowArgs()"));
        require(ok, "legacyNarrowArgs reverted unexpectedly");
    }
    // Property 18: emitNestedExternalArg has no unexpected revert
    function testAuto_EmitNestedExternalArg_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("emitNestedExternalArg()"));
        require(ok, "emitNestedExternalArg reverted unexpectedly");
    }
    // Property 19: customErrorNestedExternalArg has no unexpected revert
    function testAuto_CustomErrorNestedExternalArg_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("customErrorNestedExternalArg()"));
        require(ok, "customErrorNestedExternalArg reverted unexpectedly");
    }
    // Property 20: consumeHelper has no unexpected revert
    function testAuto_ConsumeHelper_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("consumeHelper(uint256)", uint256(1)));
        require(ok, "consumeHelper reverted unexpectedly");
    }
    // Property 21: helperNestedExternalArg has no unexpected revert
    function testAuto_HelperNestedExternalArg_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("helperNestedExternalArg()"));
        require(ok, "helperNestedExternalArg reverted unexpectedly");
    }
    // Property 22: ecmNestedExternalArg has no unexpected revert
    function testAuto_EcmNestedExternalArg_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("ecmNestedExternalArg()"));
        require(ok, "ecmNestedExternalArg reverted unexpectedly");
    }
    // Property 23: TODO decode and assert `erc20BalanceNestedExternalArg` result
    function testTODO_Erc20BalanceNestedExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("erc20BalanceNestedExternalArg()"));
        require(ok, "erc20BalanceNestedExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "erc20BalanceNestedExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 24: TODO decode and assert `erc20AllowanceNestedExternalArg` result
    function testTODO_Erc20AllowanceNestedExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("erc20AllowanceNestedExternalArg()"));
        require(ok, "erc20AllowanceNestedExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "erc20AllowanceNestedExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 25: TODO decode and assert `erc20SupplyNestedExternalArg` result
    function testTODO_Erc20SupplyNestedExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("erc20SupplyNestedExternalArg()"));
        require(ok, "erc20SupplyNestedExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "erc20SupplyNestedExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 26: TODO decode and assert `mappingNestedExternalArg` result
    function testTODO_MappingNestedExternalArg_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("mappingNestedExternalArg()"));
        require(ok, "mappingNestedExternalArg reverted unexpectedly");
        assertEq(ret.length, 32, "mappingNestedExternalArg ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 27: TODO decode and assert `pureDirtyInt` result
    function testTODO_PureDirtyInt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pureDirtyInt()"));
        require(ok, "pureDirtyInt reverted unexpectedly");
        assertEq(ret.length, 32, "pureDirtyInt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 28: TODO decode and assert `bindDirtyInt` result
    function testTODO_BindDirtyInt_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bindDirtyInt()"));
        require(ok, "bindDirtyInt reverted unexpectedly");
        assertEq(ret.length, 32, "bindDirtyInt ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 29: TODO decode and assert `pureDirtyBytes` result
    function testTODO_PureDirtyBytes_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("pureDirtyBytes()"));
        require(ok, "pureDirtyBytes reverted unexpectedly");
        assertEq(ret.length, 32, "pureDirtyBytes ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
    // Property 30: TODO decode and assert `bindDirtyBytes` result
    function testTODO_BindDirtyBytes_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("bindDirtyBytes()"));
        require(ok, "bindDirtyBytes reverted unexpectedly");
        assertEq(ret.length, 32, "bindDirtyBytes ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
