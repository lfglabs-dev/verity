// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Solidity 0.8 checked `int256` arithmetic: the reference for revert payloads
/// (`Panic(0x11)` on overflow, `Panic(0x12)` on division by zero) and results.
contract Int256CheckedSmokeReference {
    int256 internal last;

    function addChecked(int256 a, int256 b) external returns (int256) {
        last = a + b;
        return last;
    }

    function subChecked(int256 a, int256 b) external returns (int256) {
        last = a - b;
        return last;
    }

    function mulChecked(int256 a, int256 b) external returns (int256) {
        last = a * b;
        return last;
    }

    function divChecked(int256 a, int256 b) external returns (int256) {
        last = a / b;
        return last;
    }

    function negChecked(int256 a) external returns (int256) {
        last = -a;
        return last;
    }

    function applyDelta(int256 delta) external returns (int256) {
        if (delta < 0) {
            last = last - (-delta);
        } else {
            last = last + delta;
        }
        return last;
    }
}

contract Int256CheckedSmokeTest is Test, YulTestBase {
    address internal yulContract;
    Int256CheckedSmokeReference internal referenceContract;

    function setUp() public {
        yulContract = deployCompiledVerityModule(
            "Contracts.Smoke.Int256CheckedSmoke",
            "Int256CheckedSmoke",
            _smokeYulDir()
        );
        referenceContract = new Int256CheckedSmokeReference();
    }

    function _assertParity(bytes memory callData) internal {
        (bool yulSuccess, bytes memory yulData) = yulContract.call(callData);
        (bool refSuccess, bytes memory refData) = address(referenceContract).call(callData);
        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "return/revert data mismatch");
    }

    function _binary(string memory sig, int256 a, int256 b) internal {
        _assertParity(abi.encodeWithSignature(sig, a, b));
    }

    function testOverflowRevertsWithPanic0x11() public {
        int256 mn = type(int256).min;
        int256 mx = type(int256).max;
        _binary("addChecked(int256,int256)", mx, 1);
        _binary("addChecked(int256,int256)", mn, -1);
        _binary("subChecked(int256,int256)", mn, 1);
        _binary("subChecked(int256,int256)", mx, -1);
        _binary("mulChecked(int256,int256)", mn, -1);
        _binary("mulChecked(int256,int256)", -1, mn);
        _binary("mulChecked(int256,int256)", int256(1) << 128, int256(1) << 127);
        _binary("divChecked(int256,int256)", mn, -1);
        _assertParity(abi.encodeWithSignature("negChecked(int256)", mn));
    }

    function testDivisionByZeroRevertsWithPanic0x12() public {
        _binary("divChecked(int256,int256)", 1, 0);
        _binary("divChecked(int256,int256)", type(int256).min, 0);
    }

    function testApplyDeltaSequence() public {
        _binary("addChecked(int256,int256)", -1, 0);
        _assertParity(abi.encodeWithSignature("applyDelta(int256)", int256(25)));
        _assertParity(abi.encodeWithSignature("applyDelta(int256)", int256(-30)));
        _assertParity(abi.encodeWithSignature("applyDelta(int256)", type(int256).min));
    }

    function testFuzzBinaryParity(int256 a, int256 b) public {
        _binary("addChecked(int256,int256)", a, b);
        _binary("subChecked(int256,int256)", a, b);
        _binary("mulChecked(int256,int256)", a, b);
        _binary("divChecked(int256,int256)", a, b);
        _assertParity(abi.encodeWithSignature("negChecked(int256)", a));
    }
}
