// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract PayloadSink {
    uint256 public lastLength;

    fallback(bytes calldata data) external payable returns (bytes memory) {
        lastLength = data.length;
        return "";
    }
}

/// Spilled locals survive a runtime-sized copy to free memory: the free pointer starts above
/// the spill area whenever the function spills.
contract SpillFreeMemorySmokeTest is Test, YulTestBase {
    address internal smoke;
    PayloadSink internal sink;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.SpillFreeMemorySmoke", "SpillFreeMemorySmoke", _smokeYulDir()
        );
        sink = new PayloadSink();
    }

    function _call(uint256 payloadLength) internal returns (uint256) {
        bytes memory data = new bytes(payloadLength);
        for (uint256 x = 0; x < payloadLength; x += 31) data[x] = 0xff;
        (bool ok, bytes memory out) = smoke.call(abi.encodeWithSignature(
            "forwardAndSum(address,uint256,uint256,uint256,bytes)", address(sink), 1, 2, 3, data));
        assertTrue(ok, "forwardAndSum reverted");
        assertEq(sink.lastLength(), payloadLength);
        return abi.decode(out, (uint256));
    }

    function testSmallPayload() public {
        assertEq(_call(100), 61);
    }

    function testPayloadLargerThanSpillGap() public {
        assertEq(_call(5000), 61);
    }
}
