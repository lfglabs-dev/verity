// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// The compiled `copyBytes` + `keccak256` and `mstore` + `keccak256` hash exactly what
/// Solidity's `keccak256(data)` / `keccak256(abi.encode(a, b))` hash.
contract MemoryHashSmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule("Contracts.Smoke.MemoryHashSmoke", "MemoryHashSmoke", _smokeYulDir());
    }

    function testFuzzHashBytes(bytes calldata data) public {
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature("hashBytes(bytes)", data));
        assertTrue(ok);
        assertEq(abi.decode(out, (bytes32)), keccak256(data));
    }

    function testFuzzHashWords(uint256 a, uint256 b) public {
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature("hashWords(uint256,uint256)", a, b));
        assertTrue(ok);
        assertEq(abi.decode(out, (bytes32)), keccak256(abi.encode(a, b)));
    }
}
