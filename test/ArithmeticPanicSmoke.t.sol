// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract ArithmeticPanicSmokeTest is Test, YulTestBase {
    address internal arithmeticPanicSmoke;

    function _decodePanicCode(bytes memory data) internal pure returns (uint256 code) {
        require(data.length == 36, "invalid Panic payload");

        uint256 selector;
        assembly {
            selector := shr(224, mload(add(data, 32)))
            code := mload(add(data, 36))
        }

        require(selector == 0x4e487b71, "not a Panic(uint256) payload");
    }

    function _assertPanicRevert(
        bytes memory callData,
        uint256 expectedCode,
        uint256 expectedBalance,
        string memory context
    ) internal {
        (bool success, bytes memory revertData) = arithmeticPanicSmoke.call(callData);

        assertFalse(success, string.concat(context, ": call should revert"));
        assertEq(_decodePanicCode(revertData), expectedCode, string.concat(context, ": unexpected panic code"));
        assertEq(
            revertData,
            abi.encodeWithSignature("Panic(uint256)", expectedCode),
            string.concat(context, ": unexpected Panic payload")
        );
        assertEq(
            readStorage(arithmeticPanicSmoke, 0),
            expectedBalance,
            string.concat(context, ": reverting call changed the stored balance")
        );
    }

    function setUp() public {
        arithmeticPanicSmoke =
            deployCompiledVerityModule("Contracts.Smoke.ArithmeticPanicSmoke", "ArithmeticPanicSmoke", _smokeYulDir());
    }

    function testDepositMaxThenOverflowRevertsWithPanic11AndRollsBack() public {
        (bool initialSuccess, bytes memory initialData) =
            arithmeticPanicSmoke.call(abi.encodeWithSignature("deposit(uint256)", type(uint256).max));

        assertTrue(initialSuccess, "depositing MAX_UINT256 should succeed");
        assertEq(abi.decode(initialData, (uint256)), type(uint256).max, "successful deposit should return MAX_UINT256");
        assertEq(readStorage(arithmeticPanicSmoke, 0), type(uint256).max, "successful deposit should store MAX_UINT256");

        (bool overflowSuccess, bytes memory overflowData) =
            arithmeticPanicSmoke.call(abi.encodeWithSignature("deposit(uint256)", uint256(1)));

        assertFalse(overflowSuccess, "MAX_UINT256 + 1 should revert");
        assertEq(
            overflowData,
            abi.encodeWithSignature("Panic(uint256)", uint256(0x11)),
            "overflow should return the canonical Panic(0x11) payload"
        );
        assertEq(_decodePanicCode(overflowData), uint256(0x11), "overflow should decode to panic code 0x11");
        assertEq(
            readStorage(arithmeticPanicSmoke, 0),
            type(uint256).max,
            "reverting overflow must leave the stored balance unchanged"
        );
    }

    function testWithdrawFromZeroRevertsWithPanic11AndRollsBack() public {
        _assertPanicRevert(
            abi.encodeWithSignature("withdraw(uint256)", uint256(1)), uint256(0x11), uint256(0), "subPanic underflow"
        );
    }

    function testScaleMaxByTwoRevertsWithPanic11AndRollsBack() public {
        (bool seedSuccess, bytes memory seedData) =
            arithmeticPanicSmoke.call(abi.encodeWithSignature("deposit(uint256)", type(uint256).max));

        assertTrue(seedSuccess, "seeding MAX_UINT256 should succeed");
        assertEq(abi.decode(seedData, (uint256)), type(uint256).max);

        _assertPanicRevert(
            abi.encodeWithSignature("scaleStored(uint256)", uint256(2)),
            uint256(0x11),
            type(uint256).max,
            "mulPanic overflow"
        );
    }

    function testShareByZeroRevertsWithPanic12AndRollsBack() public {
        uint256 initialBalance = 42;
        (bool seedSuccess, bytes memory seedData) =
            arithmeticPanicSmoke.call(abi.encodeWithSignature("deposit(uint256)", initialBalance));

        assertTrue(seedSuccess, "seeding the balance should succeed");
        assertEq(abi.decode(seedData, (uint256)), initialBalance);

        _assertPanicRevert(
            abi.encodeWithSignature("shareStored(uint256)", uint256(0)),
            uint256(0x12),
            initialBalance,
            "divPanic division by zero"
        );
    }
}
