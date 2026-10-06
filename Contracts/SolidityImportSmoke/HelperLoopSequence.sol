// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);
    function accumulate(uint256 bound) internal returns (uint256) {
        uint256 total;
        for (uint256 i = 0; i < bound; i++) {
            {
                uint256 term = i + 1;
                for (uint256 j = 0; j < 1; j++) {
                    if (i < bound) total = total + term;
                    else total = total + 100;
                }
            }
            value = total;
            emit Changed(value);
        }
        return total;
    }
    function change(uint256 x) external returns (uint256) {
        require(x <= 8, "bound");
        uint256 result = accumulate(x);
        // The helper return must resume here, not return from change.
        value = result + 10;
        emit Changed(value);
        return value;
    }
    function fail() external view {
        uint256 count;
        for (uint256 i = 0; i < 2; i++) { count = count + 1; }
        require(count == 0, "loop revert");
    }
    function read() external view returns (uint256) { return value; }
}
