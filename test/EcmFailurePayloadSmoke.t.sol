// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Receives plain ETH calls; reverts in the shape chosen per test, or accepts.
contract FailingCallee {
    error Refused(uint256 code);

    uint8 public mode;

    function setMode(uint8 m) external {
        mode = m;
    }

    fallback() external payable {
        if (mode == 0) revert Refused(7);
        if (mode == 1) revert("callee: denied");
        if (mode == 2) {
            assembly {
                revert(0, 0)
            }
        }
        if (mode == 3) {
            assembly {
                mstore(0, 0x0102030405000000000000000000000000000000000000000000000000000000)
                revert(0, 5)
            }
        }
        // mode 4: accept
    }
}

/// A failed `callWithValue` ECM call re-raises the callee's revert bytes unchanged, and an
/// unfunded one reverts with no bytes, as `Contracts/Smoke/EcmFailurePayloadSmoke.lean`
/// proves of the EDSL (`failurePayload`, `ecmFailedPayload`, `ecmUnfundedPayload`).
contract EcmFailurePayloadSmokeTest is Test, YulTestBase {
    address internal smoke;
    FailingCallee internal callee;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.EcmFailurePayloadSmoke", "EcmFailurePayloadSmoke", _smokeYulDir()
        );
        callee = new FailingCallee();
        vm.deal(smoke, 1);
    }

    function _forward(uint256 value) internal returns (bool, bytes memory) {
        return smoke.call(abi.encodeWithSignature("forward(address,uint256)", address(callee), value));
    }

    function _assertBubbles(uint8 mode, uint256 expectedLength) internal {
        callee.setMode(mode);
        (bool ok, bytes memory expected) = address(callee).call("");
        assertFalse(ok, "callee must revert");
        assertEq(expected.length, expectedLength, "callee payload length");

        bytes memory data;
        (ok, data) = _forward(1);
        assertFalse(ok, "forward must revert");
        assertEq(data, expected, "forward re-raises the callee bytes");
    }

    function testCustomErrorBubbles() public {
        _assertBubbles(0, 36);
    }

    function testErrorStringBubbles() public {
        _assertBubbles(1, 100);
    }

    function testEmptyRevertBubbles() public {
        _assertBubbles(2, 0);
    }

    function testOddLengthRevertBubbles() public {
        _assertBubbles(3, 5);
    }

    /// Positive control: a funded call to an accepting callee succeeds and moves the wei.
    function testFundedCallSucceeds() public {
        callee.setMode(4);
        (bool ok,) = _forward(1);
        assertTrue(ok, "forward succeeds");
        assertEq(address(callee).balance, 1, "the wei moved");
    }

    /// The contract holds 1 wei; sending 2 fails at the EVM call with empty returndata,
    /// which the module bubbles: no revert bytes, not `Error("insufficient balance")`.
    function testUnfundedCallRevertsEmpty() public {
        callee.setMode(4);
        (bool ok, bytes memory data) = _forward(2);
        assertFalse(ok, "forward must revert");
        assertEq(data.length, 0, "no revert bytes");
    }
}
