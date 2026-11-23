// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// End-to-end check of a section that the spill pass does rewrite on the CLI path: the compiled
/// Yul must contain spill words at 4096 (the test fails if the pass stops spilling here), and
/// both functions, which share those words across dispatch cases, must return exactly what the
/// unspilled computation returns.
contract SpillStaticMemorySmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.SpillStaticMemorySmoke", "SpillStaticMemorySmoke", _smokeYulDir()
        );
    }

    function testSectionIsSpilled() public view {
        string memory yul =
            vm.readFile(string.concat(_smokeYulDir(), "/SpillStaticMemorySmoke.yul"));
        assertTrue(vm.contains(yul, "mstore(4096, "), "runtime section is not spilled");
        assertTrue(vm.contains(yul, "mload(4096)"), "spilled word is never read");
    }

    function _addChain(uint256 a, uint256 b, uint256 c) internal pure returns (uint256 r, uint256 s13) {
        unchecked {
            uint256 s1 = a + b;
            uint256 s5 = s1 + c + a + b + c;
            uint256 s9 = s5 + a + b + c + a;
            s13 = s9 + b + c + a + b;
            r = s13 + (s1 + (s5 + s9));
        }
    }

    function _xorChain(uint256 a, uint256 b, uint256 c) internal pure returns (uint256 r, uint256 x13) {
        unchecked {
            uint256 x1 = a ^ b;
            uint256 x5 = (((x1 + c) ^ a) + b) ^ c;
            uint256 x9 = (((x5 + a) ^ b) + c) ^ a;
            x13 = (((x9 + b) ^ c) + a) ^ b;
            r = x13 + (x1 + (x5 + x9));
        }
    }

    function _call(string memory sig, uint256 a, uint256 b, uint256 c) internal returns (uint256) {
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature(sig, a, b, c));
        assertTrue(ok, "call reverted");
        assertEq(out.length, 32);
        return abi.decode(out, (uint256));
    }

    function testAddChain() public {
        (uint256 r, uint256 s13) = _addChain(1, 2, 3);
        assertEq(r, 61);
        assertEq(_call("addChain(uint256,uint256,uint256)", 1, 2, 3), r);
        assertEq(vm.load(smoke, bytes32(0)), bytes32(s13));
    }

    function testXorChain() public {
        (uint256 r, uint256 x13) = _xorChain(5, 9, 17);
        assertEq(_call("xorChain(uint256,uint256,uint256)", 5, 9, 17), r);
        assertEq(vm.load(smoke, bytes32(0)), bytes32(x13));
    }

    function testFuzzBothChains(uint256 a, uint256 b, uint256 c) public {
        (uint256 r1,) = _addChain(a, b, c);
        assertEq(_call("addChain(uint256,uint256,uint256)", a, b, c), r1);
        (uint256 r2,) = _xorChain(a, b, c);
        assertEq(_call("xorChain(uint256,uint256,uint256)", a, b, c), r2);
    }
}
