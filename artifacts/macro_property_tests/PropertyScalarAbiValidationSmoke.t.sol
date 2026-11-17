// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyScalarAbiValidationSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ScalarAbiValidationSmoke.lean
 */
contract PropertyScalarAbiValidationSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ScalarAbiValidationSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: echoAddress returns the direct parameter value
    function testAuto_EchoAddress_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoAddress(address)", alice));
        require(ok, "echoAddress reverted unexpectedly");
        assertEq(ret.length, 32, "echoAddress ABI return length mismatch (expected 32 bytes)");
        address actual = abi.decode(ret, (address));
        assertEq(actual, alice, "echoAddress should preserve the expected value");
    }
    // Property 2: echoBool returns the direct parameter value
    function testAuto_EchoBool_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoBool(bool)", true));
        require(ok, "echoBool reverted unexpectedly");
        assertEq(ret.length, 32, "echoBool ABI return length mismatch (expected 32 bytes)");
        bool actual = abi.decode(ret, (bool));
        assertEq(actual, true, "echoBool should preserve the expected value");
    }
    // Property 3: echoBytes4 returns the direct parameter value
    function testAuto_EchoBytes4_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoBytes4(bytes4)", bytes4(uint32(0x01))));
        require(ok, "echoBytes4 reverted unexpectedly");
        assertEq(ret.length, 32, "echoBytes4 ABI return length mismatch (expected 32 bytes)");
        bytes4 actual = abi.decode(ret, (bytes4));
        assertEq(actual, bytes4(uint32(0x01)), "echoBytes4 should preserve the expected value");
    }
    // Property 4: echoUint8 returns the direct parameter value
    function testAuto_EchoUint8_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoUint8(uint8)", uint8(27)));
        require(ok, "echoUint8 reverted unexpectedly");
        assertEq(ret.length, 32, "echoUint8 ABI return length mismatch (expected 32 bytes)");
        uint8 actual = abi.decode(ret, (uint8));
        assertEq(actual, uint8(27), "echoUint8 should preserve the expected value");
    }
    // Property 5: echoUint16 returns the direct parameter value
    function testAuto_EchoUint16_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoUint16(uint16)", uint16(1)));
        require(ok, "echoUint16 reverted unexpectedly");
        assertEq(ret.length, 32, "echoUint16 ABI return length mismatch (expected 32 bytes)");
        uint16 actual = abi.decode(ret, (uint16));
        assertEq(actual, uint16(1), "echoUint16 should preserve the expected value");
    }
    // Property 6: echoUint32 returns the direct parameter value
    function testAuto_EchoUint32_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoUint32(uint32)", uint32(1)));
        require(ok, "echoUint32 reverted unexpectedly");
        assertEq(ret.length, 32, "echoUint32 ABI return length mismatch (expected 32 bytes)");
        uint32 actual = abi.decode(ret, (uint32));
        assertEq(actual, uint32(1), "echoUint32 should preserve the expected value");
    }
    // Property 7: echoInt8 returns the direct parameter value
    function testAuto_EchoInt8_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoInt8(int8)", int8(1)));
        require(ok, "echoInt8 reverted unexpectedly");
        assertEq(ret.length, 32, "echoInt8 ABI return length mismatch (expected 32 bytes)");
        int8 actual = abi.decode(ret, (int8));
        assertEq(actual, int8(1), "echoInt8 should preserve the expected value");
    }
    // Property 8: echoInt16 returns the direct parameter value
    function testAuto_EchoInt16_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoInt16(int16)", int16(1)));
        require(ok, "echoInt16 reverted unexpectedly");
        assertEq(ret.length, 32, "echoInt16 ABI return length mismatch (expected 32 bytes)");
        int16 actual = abi.decode(ret, (int16));
        assertEq(actual, int16(1), "echoInt16 should preserve the expected value");
    }
    // Property 9: echoUint256 returns the direct parameter value
    function testAuto_EchoUint256_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoUint256(uint256)", uint256(1)));
        require(ok, "echoUint256 reverted unexpectedly");
        assertEq(ret.length, 32, "echoUint256 ABI return length mismatch (expected 32 bytes)");
        uint256 actual = abi.decode(ret, (uint256));
        assertEq(actual, uint256(1), "echoUint256 should preserve the expected value");
    }
    // Property 10: echoInt256 returns the direct parameter value
    function testAuto_EchoInt256_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoInt256(int256)", int256(1)));
        require(ok, "echoInt256 reverted unexpectedly");
        assertEq(ret.length, 32, "echoInt256 ABI return length mismatch (expected 32 bytes)");
        int256 actual = abi.decode(ret, (int256));
        assertEq(actual, int256(1), "echoInt256 should preserve the expected value");
    }
    // Property 11: echoBytes32 returns the direct parameter value
    function testAuto_EchoBytes32_ReturnsDirectParam() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("echoBytes32(bytes32)", bytes32(uint256(0xBEEF))));
        require(ok, "echoBytes32 reverted unexpectedly");
        assertEq(ret.length, 32, "echoBytes32 ABI return length mismatch (expected 32 bytes)");
        bytes32 actual = abi.decode(ret, (bytes32));
        assertEq(actual, bytes32(uint256(0xBEEF)), "echoBytes32 should preserve the expected value");
    }
    // Property 12: TODO decode and assert `accountOfPair` result
    function testTODO_AccountOfPair_DecodeAndAssert() public {
        vm.prank(alice);
        (bool ok, bytes memory ret) = target.call(abi.encodeWithSignature("accountOfPair((uint256,address))", abi.decode(abi.encode(uint256(1), alice), (uint256, address))));
        require(ok, "accountOfPair reverted unexpectedly");
        assertEq(ret.length, 32, "accountOfPair ABI return length mismatch (expected 32 bytes)");
        // TODO(#1011): decode `ret` and assert the concrete postcondition from Lean theorem.
        ret;
    }
}
