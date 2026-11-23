// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// A function with more than `defaultMaxStackLocals` locals returns a calldata array: the ABI
/// encoding is written from memory address 0 with a runtime size. The compiled contract must
/// return the whole array for every length, including arrays whose encoding reaches past the
/// fixed spill words at 4096 (more than 126 elements). A spill of the array's length or data
/// offset to such a word would be overwritten by the copy and truncate the return data.
contract SpillReturnArraySmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.SpillReturnArraySmoke", "SpillReturnArraySmoke", _smokeYulDir()
        );
    }

    function _values(uint256 length) internal pure returns (uint256[] memory values) {
        values = new uint256[](length);
        for (uint256 i = 0; i < length; i++) values[i] = i;
    }

    function _echo(uint256 length) internal {
        uint256[] memory values = _values(length);
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature(
            "echoAfterWork(uint256,uint256,uint256,uint256,uint256[])", 2, 3, 5, 7, values));
        assertTrue(ok, "echoAfterWork reverted");
        assertEq(out.length, 64 + 32 * length, "return data length");
        assertEq(out, abi.encode(values), "return data");
        assertEq(vm.load(smoke, bytes32(uint256(0))), bytes32(uint256(17)));
        assertEq(vm.load(smoke, bytes32(uint256(1))), bytes32(uint256(6)));
        assertEq(vm.load(smoke, bytes32(uint256(5))), bytes32(uint256(9)));
    }

    function testShortArray() public {
        _echo(3);
    }

    function testArrayReachingSpillWords() public {
        _echo(127);
    }

    function testArrayPastSpillWords() public {
        _echo(200);
    }
}
