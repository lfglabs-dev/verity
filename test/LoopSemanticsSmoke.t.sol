// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// The bytecode gives the values the EDSL theorems in `Contracts/Smoke/LoopSemanticsSmoke.lean`
/// state for the same loops.
contract LoopSemanticsSmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.LoopSemanticsSmoke", "LoopSemanticsSmoke", _smokeYulDir()
        );
    }

    function _call(string memory sig, uint256 arg) internal returns (uint256) {
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature(sig, arg));
        assertTrue(ok, sig);
        return abi.decode(out, (uint256));
    }

    function testSumBelow() public {
        assertEq(_call("sumBelow(uint256)", 10), 45);
        assertEq(_call("sumBelow(uint256)", 0), 0);
    }

    function testIsqrt() public {
        assertEq(_call("isqrt(uint256)", 1000000), 1000);
        assertEq(_call("isqrt(uint256)", 3), 1);
    }

    function testSetBitTrace() public {
        assertEq(_call("setBitTrace(uint256)", 530), 590849);
    }

    function testIsqrtFuzz(uint256 n) public {
        uint256 z = _call("isqrt(uint256)", n);
        assertLe(z * z, n);
        if (z < type(uint128).max) assertGt((z + 1) * (z + 1), n);
    }
}
