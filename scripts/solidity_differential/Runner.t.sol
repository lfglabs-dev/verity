// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface VmSlice {
    function readFile(string calldata) external view returns (string memory);
    function readFileBinary(string calldata) external view returns (bytes memory);
    function writeFile(string calldata, string calldata) external;
    function writeLine(string calldata, string calldata) external;
    function parseJsonString(string calldata, string calldata) external pure returns (string memory);
    function parseJsonUint(string calldata, string calldata) external pure returns (uint256);
    function parseJsonBytes(string calldata, string calldata) external pure returns (bytes memory);
    function parseUint(string calldata) external pure returns (uint256);
    function toString(uint256) external pure returns (string memory);
    function toString(bytes calldata) external pure returns (string memory);
    function store(address, bytes32, bytes32) external;
    function load(address, bytes32) external view returns (bytes32);
    function warp(uint256) external;
    function snapshotState() external returns (uint256);
    function revertToStateAndDelete(uint256) external returns (bool);
    function record() external;
    function accesses(address) external returns (bytes32[] memory, bytes32[] memory);
}

/// Executes the actual creation/runtime bytecode. No contract arithmetic or
/// storage layout logic is duplicated here. All slices in v1 are read-only.
contract SliceDifferentialTest {
    VmSlice constant vm = VmSlice(address(uint160(uint256(keccak256("hevm cheat code")))));
    uint256 constant CALL_GAS = 30_000_000;

    function deploy(string memory path) internal returns (address target) {
        bytes memory code = vm.readFileBinary(path);
        assembly { target := create(0, add(code, 32), mload(code)) }
        require(target != address(0) && target.code.length != 0, "harness: deployment failed");
    }

    function number(string memory json, string memory key) internal pure returns (uint256) {
        return vm.parseUint(vm.parseJsonString(json, key));
    }

    function runRoute(string memory route, address target, uint256 count) internal {
        string memory output = string.concat("out/", route, ".txt");
        vm.writeFile(output, "");
        for (uint256 i; i < count; ++i) {
            uint256 snapshot = vm.snapshotState();
            string memory json = vm.readFile(string.concat("evm-cases/", vm.toString(i), ".json"));
            string memory prefix = "";
            uint256 entries = vm.parseJsonUint(json, string.concat(prefix, ".storageCount"));
            for (uint256 k; k < entries; ++k) {
                string memory row = string.concat(prefix, ".storage[", vm.toString(k), "]");
                vm.store(target, bytes32(number(json, string.concat(row, "[0]"))),
                    bytes32(number(json, string.concat(row, "[1]"))));
            }
            vm.warp(number(json, string.concat(prefix, ".timestamp")));
            bytes memory data = vm.parseJsonBytes(json, string.concat(prefix, ".", route, "Calldata"));
            vm.record();
            uint256 beforeGas = gasleft();
            (bool ok, bytes memory returned) = target.call{gas: CALL_GAS}(data);
            uint256 spent = beforeGas - gasleft();
            // Exhausted gas or exceptional halts are resource/harness failures,
            // never evidence that the Solidity and model both reverted.
            require(spent < CALL_GAS, "harness: execution resource limit");
            (, bytes32[] memory writes) = vm.accesses(target);
            require(writes.length == 0, "harness: read-only slice wrote storage");
            string memory slots;
            uint256 observed = vm.parseJsonUint(json, string.concat(prefix, ".observeCount"));
            for (uint256 k; k < observed; ++k) {
                uint256 slot = number(json, string.concat(prefix, ".observe[", vm.toString(k), "]"));
                slots = string.concat(slots, " ", vm.toString(uint256(vm.load(target, bytes32(slot)))));
            }
            vm.writeLine(output, string.concat(vm.toString(i), ok ? " ok " : " revert ", vm.toString(returned), slots));
            require(vm.revertToStateAndDelete(snapshot), "harness: snapshot restore failed");
        }
    }

    function test_differential() public {
        uint256 count = vm.parseJsonUint(vm.readFile("cases.json"), ".count");
        runRoute("source", deploy("source.bin"), count);
        runRoute("compiled", deploy("compiled.bin"), count);
    }
}
