// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Instrument fixture paired with the handwritten SequenceModel, not an import claim.
contract SequenceFixture {
    uint256 private stored;
    function change(uint256 value) external returns (uint256 old) {
        old = stored;
        stored = value;
        return old;
    }
    function fail() external {
        stored = 99;
        assert(false);
    }
    function read() external view returns (uint256) {
        return stored;
    }
}
