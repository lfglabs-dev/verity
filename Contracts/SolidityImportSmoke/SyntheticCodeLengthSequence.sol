// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Emptiness tests of the executing contract's own code (the initializer / constructor guard):
// at runtime the account has code on both EVM routes, so every test sees nonempty code.
contract SequenceFixture {
    uint256 private total;

    function _isConstructing() private view returns (bool) {
        return address(this).code.length == 0;
    }

    function change(uint256 x) external returns (uint256) {
        require(address(this).code.length != 0, "constructing");
        if (_isConstructing()) total = total + 1000;
        if (address(this).code.length > 0) total = total + x % 7;
        if (0 == address(this).code.length) total = total + 100;
        return total;
    }

    // The stateful harness's reverting call: its write is rolled back.
    function fail() external {
        total = total + 1;
        revert();
    }

    function read() external view returns (uint256) {
        return total;
    }
}
