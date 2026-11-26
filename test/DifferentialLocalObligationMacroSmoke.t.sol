// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import {console2} from "forge-std/Test.sol";
import "./DiffTestConfig.sol";
import "./yul/YulTestBase.sol";
import "./DifferentialTestBase.sol";

contract DifferentialLocalObligationMacroSmoke is YulTestBase, DiffTestConfig, DifferentialTestBase {
    address macroSmoke;
    mapping(uint256 => uint256) edslStorage;

    function setUp() public {
        macroSmoke = deployYul("LocalObligationMacroSmoke");
        require(macroSmoke != address(0), "Deploy failed");
    }

    function executeDifferentialTest(address sender, uint256 arg0) internal returns (bool success) {
        vm.prank(sender);
        (bool evmSuccess, bytes memory evmReturnData) = macroSmoke.call(
            abi.encodeWithSignature("dischargedEdge(uint256)", arg0)
        );

        uint256 evmStorageAfter = uint256(vm.load(macroSmoke, bytes32(uint256(1))));
        uint256 evmReturnValue = evmSuccess && evmReturnData.length > 0 ? abi.decode(evmReturnData, (uint256)) : 0;

        string memory edslResult = _runInterpreter(sender, arg0, _buildStorageString());
        bool edslSuccess = contains(edslResult, "\"success\":true");
        uint256 edslReturnValue = _extractReturnValue(edslResult);
        (bool hasStorageChange, uint256 edslStorageChange) = _extractStorageChange(edslResult, 1);
        if (hasStorageChange) {
            edslStorage[1] = edslStorageChange;
        }

        if (evmSuccess != edslSuccess) {
            console2.log("MISMATCH: success flags differ");
            testsFailed++;
            return false;
        }

        // Validate: revert bytes must match
        if (!_revertDataMatches(evmSuccess, evmReturnData, edslResult)) {
            testsFailed++;
            return false;
        }
        if (evmReturnValue != edslReturnValue) {
            console2.log("MISMATCH: return values differ");
            testsFailed++;
            return false;
        }
        if (evmStorageAfter != edslStorage[1]) {
            console2.log("MISMATCH: slot 1 differs");
            testsFailed++;
            return false;
        }

        testsPassed++;
        return true;
    }

    function _runInterpreter(
        address sender,
        uint256 arg0,
        string memory storageState
    ) internal returns (string memory) {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = string.concat(
            _interpreterPreamble(),
            " LocalObligationMacroSmoke dischargedEdge ",
            vm.toString(sender),
            " ",
            vm.toString(arg0),
            " \"",
            storageState,
            "\"",
            " value=0 timestamp=",
            vm.toString(block.timestamp)
        );
        return string(vm.ffi(inputs));
    }

    function _buildStorageString() internal view returns (string memory) {
        uint256 val = edslStorage[1];
        if (val == 0) {
            return "";
        }
        return string.concat("1:", vm.toString(val));
    }

    function testDifferential_DischargedEdge_Basic(uint256 value) public {
        bool success = executeDifferentialTest(address(0xA11CE), value);
        assertTrue(success, "dischargedEdge differential test failed");
    }
}
