// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./DifferentialTestBase.sol";
import "./yul/YulTestBase.sol";

contract CryptoHashReference {
    uint256 public lastHash;

    function storeHashTwo(uint256 a, uint256 b) external {
        unchecked {
            lastHash = a + b;
        }
    }

    function storeHashThree(uint256 a, uint256 b, uint256 c) external {
        unchecked {
            lastHash = a + b + c;
        }
    }

    function getLastHash() external view returns (uint256) {
        return lastHash;
    }
}

/**
 * @title DifferentialCryptoHash
 * @notice Differential tests for CryptoHash against the Lean interpreter.
 */
contract DifferentialCryptoHash is YulTestBase, DiffTestConfig, DifferentialTestBase {
    CryptoHashReference referenceContract;

    // Storage state tracking for EDSL interpreter
    mapping(uint256 => uint256) edslStorage;

    function setUp() public {
        referenceContract = new CryptoHashReference();
    }

    function executeDifferentialTest(
        string memory functionName,
        address sender,
        uint256 a,
        uint256 b,
        uint256 c,
        uint256 argCount
    ) internal returns (bool success) {
        vm.prank(sender);

        bool evmSuccess;
        bytes memory evmReturnData;

        bytes32 functionSig = keccak256(bytes(functionName));
        if (functionSig == keccak256(bytes("storeHashTwo"))) {
            (evmSuccess, evmReturnData) = address(referenceContract).call(
                abi.encodeWithSignature("storeHashTwo(uint256,uint256)", a, b)
            );
        } else if (functionSig == keccak256(bytes("storeHashThree"))) {
            (evmSuccess, evmReturnData) = address(referenceContract).call(
                abi.encodeWithSignature("storeHashThree(uint256,uint256,uint256)", a, b, c)
            );
        } else if (functionSig == keccak256(bytes("getLastHash"))) {
            (evmSuccess, evmReturnData) = address(referenceContract).call(
                abi.encodeWithSignature("getLastHash()")
            );
        } else {
            revert("Unknown function");
        }

        uint256 evmStorageAfter = uint256(vm.load(address(referenceContract), bytes32(uint256(0))));
        uint256 evmReturnValue = evmSuccess && evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        string memory storageState = _buildStorageString();
        string memory edslResult = _runInterpreter(functionName, sender, a, b, c, argCount, storageState);

        bool verbose = _diffVerbose();
        if (verbose) {
            console2.log("EVM success:", evmSuccess);
            console2.log("EVM storage[0]:", evmStorageAfter);
            console2.log("EVM return value:", evmReturnValue);
            console2.log("EDSL result:", edslResult);
        }

        bool edslSuccess = contains(edslResult, '"success":true');

        if (!contains(edslResult, '"returnValue":')) {
            console2.log("ERROR: Malformed JSON - missing returnValue field");
            console2.log("  JSON:", edslResult);
            testsFailed++;
            return false;
        }

        uint256 edslReturnValue = _extractReturnValue(edslResult);

        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH: Success flags differ!");
            console2.log("  EVM:", evmSuccess);
            console2.log("  EDSL:", edslSuccess);
            testsFailed++;
            return false;
        }

        // Validate: revert bytes must match
        if (!_revertDataMatches(evmSuccess, evmReturnData, edslResult)) {
            testsFailed++;
            return false;
        }

        if (evmReturnValue != edslReturnValue) {
            console2.log("MISMATCH: Return values differ!");
            console2.log("  EVM:", evmReturnValue);
            console2.log("  EDSL:", edslReturnValue);
            testsFailed++;
            return false;
        }

        (bool hasStorageChange, uint256 edslStorageChange) = _extractStorageChange(edslResult, 0);
        if (hasStorageChange) {
            edslStorage[0] = edslStorageChange;
        }

        if (evmStorageAfter != edslStorage[0]) {
            console2.log("MISMATCH: Storage states differ!");
            console2.log("  EVM storage[0]:", evmStorageAfter);
            console2.log("  EDSL storage[0]:", edslStorage[0]);
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        string memory functionName,
        address sender,
        uint256 a,
        uint256 b,
        uint256 c,
        uint256 argCount,
        string memory storageState
    ) internal returns (string memory) {
        string memory argPart = "";
        if (argCount >= 1) {
            argPart = string.concat(argPart, " ", vm.toString(a));
        }
        if (argCount >= 2) {
            argPart = string.concat(argPart, " ", vm.toString(b));
        }
        if (argCount >= 3) {
            argPart = string.concat(argPart, " ", vm.toString(c));
        }

        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = string.concat(
            _interpreterPreamble(),
            " CryptoHash ",
            functionName,
            " ",
            vm.toString(sender),
            argPart,
            bytes(storageState).length > 0 ? string.concat(" \"", storageState, "\"") : "",
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );

        bytes memory edslResultBytes = vm.ffi(inputs);
        return string(edslResultBytes);
    }

    function _buildStorageString() internal view returns (string memory) {
        uint256 val = edslStorage[0];
        if (val == 0) {
            return "";
        }
        return string.concat("0:", vm.toString(val));
    }

    function testDifferential_BasicOperations() public {
        bool success1 = executeDifferentialTest("storeHashTwo", address(0xA11CE), 100, 200, 0, 2);
        assertTrue(success1, "storeHashTwo failed");

        bool success2 = executeDifferentialTest("getLastHash", address(0xA11CE), 0, 0, 0, 0);
        assertTrue(success2, "getLastHash after storeHashTwo failed");

        bool success3 = executeDifferentialTest("storeHashThree", address(0xB0B), 7, 8, 9, 3);
        assertTrue(success3, "storeHashThree failed");

        bool success4 = executeDifferentialTest("getLastHash", address(0xB0B), 0, 0, 0, 0);
        assertTrue(success4, "getLastHash after storeHashThree failed");
    }

    function testDifferential_EdgeValues() public {
        uint256[] memory values = _edgeUintValues();
        address sender = address(0xA11CE);

        for (uint256 i = 0; i < values.length; i++) {
            bool s2 = executeDifferentialTest("storeHashTwo", sender, values[i], 1, 0, 2);
            assertTrue(s2, "Edge storeHashTwo failed");

            bool s3 = executeDifferentialTest("storeHashThree", sender, values[i], 1, 2, 3);
            assertTrue(s3, "Edge storeHashThree failed");
        }
    }

    function testDifferential_Random100() public {
        (uint256 startIndex, uint256 count) = _diffRandomSmallRange();
        _runRandomDifferentialTests(startIndex, count, _diffRandomSeed("CryptoHash"));
    }

    function _runRandomDifferentialTests(uint256 startIndex, uint256 count, uint256 seed) internal {
        uint256 prng = _skipRandom(seed, startIndex);

        vm.pauseGasMetering();
        for (uint256 i = 0; i < count; i++) {
            prng = _lcg(prng);
            address sender = _indexToAddress(prng % 5);

            prng = _lcg(prng);
            uint256 choice = prng % 3;

            if (choice == 0) {
                prng = _lcg(prng);
                uint256 a = _coerceRandomUint256(prng, 1_000_000);
                prng = _lcg(prng);
                uint256 b = _coerceRandomUint256(prng, 1_000_000);
                bool ok = executeDifferentialTest("storeHashTwo", sender, a, b, 0, 2);
                assertTrue(ok, "Random storeHashTwo failed");
            } else if (choice == 1) {
                prng = _lcg(prng);
                uint256 a = _coerceRandomUint256(prng, 1_000_000);
                prng = _lcg(prng);
                uint256 b = _coerceRandomUint256(prng, 1_000_000);
                prng = _lcg(prng);
                uint256 c = _coerceRandomUint256(prng, 1_000_000);
                bool ok = executeDifferentialTest("storeHashThree", sender, a, b, c, 3);
                assertTrue(ok, "Random storeHashThree failed");
            } else {
                bool ok = executeDifferentialTest("getLastHash", sender, 0, 0, 0, 0);
                assertTrue(ok, "Random getLastHash failed");
            }
        }
        vm.resumeGasMetering();

        assertEq(testsFailed, 0, "Some random tests failed");
    }
}
