// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/**
 * @title ConstructorArgsTrailingBytesTest
 * @notice Bytes appended after the ABI-encoded constructor arguments must be inert.
 * @dev The deploy block copies every trailing initcode byte into memory before
 *      decoding the arguments. Copied to offset 0, a tail longer than 64 bytes
 *      overwrote the free-memory pointer (64..95), and the constructor's event
 *      emission then wrote through a deployer-chosen pointer (out of gas at
 *      2^248, quadratic memory expansion below that). The arguments now land
 *      at the free pointer, which is bumped past them, as in solc.
 *
 *      Contract under test: `ConstructorEventSmoke`
 *      (Contracts/Smoke/ConstructorEventSmoke.lean): the constructor stores
 *      its `Uint256` argument and emits `Stored(value)`.
 */
contract ConstructorArgsTrailingBytesTest is Test, YulTestBase {
    uint256 internal constant ARG = 1000;

    event Stored(uint256 value);

    function _initCode() internal returns (bytes memory) {
        _ensureVerityModuleYul("Contracts.Smoke.ConstructorEventSmoke", "ConstructorEventSmoke", _smokeYulDir());
        return _compileYul(string.concat(_smokeYulDir(), "/ConstructorEventSmoke.yul"));
    }

    /// Deploy with `tail` appended after the ABI-encoded argument. With
    /// `boundGas`, the tail's content must not change the deployment gas
    /// measured against an all-zero tail of the same length: a tail word read
    /// as the free-memory pointer would expand memory up to it. (Forge's gas
    /// accounting for `create` also grows with the number of nonzero initcode
    /// bytes, so long tails are not gas-compared.)
    function _deployWithTail(bytes memory tail, bool boundGas) internal {
        bytes memory initCode = _initCode();
        uint256 before = gasleft();
        _deploy(bytes.concat(initCode, abi.encode(ARG), new bytes(tail.length)));
        uint256 zeroTailGas = before - gasleft();

        vm.expectEmit(true, true, true, true);
        emit Stored(ARG);
        before = gasleft();
        address target = _deploy(bytes.concat(initCode, abi.encode(ARG), tail));
        uint256 tailGas = before - gasleft();

        (bool ok, bytes memory ret) = target.staticcall(abi.encodeWithSignature("get()"));
        require(ok, "get reverted");
        assertEq(abi.decode(ret, (uint256)), ARG, "stored argument");
        if (boundGas) assertLe(tailGas, zeroTailGas + 2000, "tail content must not expand memory");
    }

    function testExactEncoding() public {
        _deployWithTail("", true);
    }

    function testExtraZeroWord() public {
        _deployWithTail(new bytes(32), true);
    }

    /// Byte 64 of a copy at offset 0 is the pointer's most significant byte.
    function testNonZeroByteAtOffset64() public {
        _deployWithTail(bytes.concat(new bytes(32), hex"01"), true);
    }

    function testPointerSizedTailWord() public {
        _deployWithTail(bytes.concat(new bytes(32), abi.encode(uint256(1) << 255)), true);
    }

    function testOneMegabyteTailWord() public {
        _deployWithTail(bytes.concat(new bytes(32), abi.encode(uint256(0x100000))), true);
    }

    function testLongTail() public {
        bytes memory tail = new bytes(4096);
        for (uint256 i = 0; i < tail.length; i++) tail[i] = 0xff;
        _deployWithTail(tail, false);
    }

    /// Fewer argument bytes than the ABI head still revert.
    function testShortArgsRevert() public {
        bytes memory initCode = bytes.concat(_initCode(), new bytes(31));
        address target;
        assembly {
            target := create(0, add(initCode, 0x20), mload(initCode))
        }
        assertEq(target, address(0), "deployment with 31 argument bytes must fail");
    }
}
