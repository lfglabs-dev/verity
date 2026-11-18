// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    string private constant NAME = "Verity";
    bytes private constant REVISION = bytes("1");
    bytes private constant NAME_BYTES = bytes(NAME);
    bytes private constant HEX_BYTES = bytes(hex"0102ff");
    string private constant ROUND_TRIP = string(bytes("ab"));

    uint256 private total;
    bytes32 private last;

    function change(uint256 x) external returns (bytes32) {
        bytes32 h = keccak256(REVISION);
        if (x % 2 == 0) {
            h = h ^ keccak256(NAME_BYTES);
        }
        if (x % 3 == 0) {
            h = h ^ keccak256(HEX_BYTES);
        }
        if (x % 5 == 0) {
            h = h ^ keccak256(bytes(ROUND_TRIP));
        }
        last = h;
        total += x % 100;
        return h;
    }

    function fail() external {
        total += 1;
        require(keccak256(REVISION) == keccak256(HEX_BYTES), "byte constants differ");
    }

    function read() external view returns (uint256, bytes32) {
        return (total, last);
    }
}
