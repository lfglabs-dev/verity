// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Reverts in a shape chosen per test, including payloads that are not whole words.
contract RevertingVault {
    error InsufficientBalance(uint256 have, uint256 want);

    uint8 public mode;

    function setMode(uint8 m) external {
        mode = m;
    }

    function _fail(uint256 amount) internal view {
        if (mode == 0) revert InsufficientBalance(7, amount);
        if (mode == 1) {
            uint256 x = type(uint256).max;
            x += amount; // Panic(0x11)
        }
        if (mode == 2) revert("vault: denied");
        if (mode == 3) {
            assembly {
                revert(0, 0)
            }
        }
        if (mode == 4) {
            assembly {
                mstore(0, 0x0102030405000000000000000000000000000000000000000000000000000000)
                revert(0, 5)
            }
        }
    }

    function withdraw(uint256 amount) external view returns (uint256) {
        _fail(amount);
        return amount;
    }

    function poke(uint256 amount) external view {
        _fail(amount);
    }
}

/// An uncaught typed interface call re-raises the callee's revert bytes unchanged
/// (`Contracts/Smoke/RevertBubbleSmoke.lean`).
contract RevertBubbleSmokeTest is Test, YulTestBase {
    address internal smoke;
    RevertingVault internal vault;

    function setUp() public {
        smoke = deployCompiledVerityModule("Contracts.Smoke.RevertBubbleSmoke", "RevertBubbleSmoke", _smokeYulDir());
        vault = new RevertingVault();
    }

    /// The bytes the vault itself reverts with in the current mode.
    function _calleeBytes(bytes memory callData) internal returns (bytes memory) {
        (bool ok, bytes memory data) = address(vault).call(callData);
        assertFalse(ok, "vault must revert");
        return data;
    }

    function _assertBubbles(uint8 mode, uint256 expectedLength) internal {
        vault.setMode(mode);
        bytes memory expected = _calleeBytes(abi.encodeWithSignature("withdraw(uint256)", 100));
        assertEq(expected.length, expectedLength, "callee payload length");

        (bool ok, bytes memory data) =
            smoke.call(abi.encodeWithSignature("pull(address,uint256)", address(vault), 100));
        assertFalse(ok, "pull must revert");
        assertEq(data, expected, "pull re-raises the callee bytes");

        (ok, data) = smoke.call(abi.encodeWithSignature("nudge(address,uint256)", address(vault), 100));
        assertFalse(ok, "nudge must revert");
        assertEq(data, expected, "nudge re-raises the callee bytes");
    }

    function testCustomErrorBubbles() public {
        _assertBubbles(0, 68);
        assertEq(
            _calleeBytes(abi.encodeWithSignature("withdraw(uint256)", 100)),
            abi.encodeWithSelector(RevertingVault.InsufficientBalance.selector, 7, 100)
        );
    }

    function testPanicBubbles() public {
        _assertBubbles(1, 36);
    }

    function testErrorStringBubbles() public {
        _assertBubbles(2, 100);
    }

    function testEmptyRevertBubbles() public {
        _assertBubbles(3, 0);
    }

    function testOddLengthRevertBubbles() public {
        _assertBubbles(4, 5);
    }
}
