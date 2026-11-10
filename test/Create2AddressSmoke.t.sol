// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// The compiled CREATE2 deploys the initcode at the EIP-1014 address the EDSL predicts.
contract Create2AddressSmokeTest is Test, YulTestBase {
    address internal smoke;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.Create2AddressSmoke", "Create2AddressSmoke", _smokeYulDir()
        );
    }

    function _deploy(bytes memory initcode, uint256 salt) internal returns (address) {
        (bool ok, bytes memory out) =
            smoke.call(abi.encodeWithSignature("deploy(bytes,uint256)", initcode, salt));
        assertTrue(ok, "deploy reverted");
        return abi.decode(out, (address));
    }

    function testFuzzDeploysAtCreate2Address(uint256 salt, uint8 runtimeByte) public {
        // initcode returning a 1-byte runtime: PUSH1 b PUSH1 0 MSTORE8 PUSH1 1 PUSH1 0 RETURN
        bytes memory initcode = abi.encodePacked(hex"60", runtimeByte, hex"60005360016000f3");
        address got = _deploy(initcode, salt);
        assertEq(got, vm.computeCreate2Address(bytes32(salt), keccak256(initcode), smoke));
        assertEq(got.code.length, 1);
    }
}
