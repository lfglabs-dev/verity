// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Named `returns (string memory name)` roots (#2737). One state variable keeps
// the importer's `stateVars.size > 1` gates off, as in the issue's stateless
// snippet, while `name = label` still copies a storage string into the result.
contract SequenceFixture {
    string private label;

    function change(uint256 x) external returns (string memory name) {
        if (x % 5 == 0) return name;
        if (x % 5 == 1) {
            name = "SequenceFixture";
        } else if (x % 5 == 2) {
            name = label;
        } else if (x % 5 == 3) {
            return "early";
        } else {
            name = string(abi.encodePacked("v", bytes32(x)));
            label = name;
        }
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external view returns (string memory current) {
        current = label;
    }
}
