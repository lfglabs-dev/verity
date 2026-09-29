// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Execution-adapter regression, not an imported-model fixture.
contract Observations {
    uint256 public stored;
    event Changed(uint256 indexed previous, uint256 current);

    function change(uint256 value) external returns (uint256 previous) {
        previous = stored;
        stored = value;
        emit Changed(previous, value);
    }

    function fail() external {
        stored = 999;
        // Make the intermediate write observable across a call before rollback.
        require(this.stored() == 999, "intermediate write");
        emit Changed(999, 999);
        revert("rolled back");
    }

    function transientProbe() external returns (uint256 previous) {
        assembly {
            previous := tload(0)
            tstore(0, 1)
        }
    }

    function catchFailure(address target) external returns (bytes memory reason) {
        (bool ok, bytes memory data) = target.call(abi.encodeCall(this.fail, ()));
        require(!ok, "expected failure");
        stored += 1;
        emit Changed(stored - 1, stored);
        return data;
    }

    function exceptional() external pure {
        assembly { invalid() }
    }
}
