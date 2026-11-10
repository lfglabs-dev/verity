// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Events with signed parameters, `int256` and narrower, indexed and not, with negative and
/// positive values, in a contract with more than one state variable. The signature (topic 0)
/// names the declared types, and every word is the sign-extended value.
contract SequenceFixture {
    uint256 private value;
    int256 private last;

    event Signed(address indexed by, int256 wide, int104 narrow);
    event SignedTopic(int24 indexed tick, int256 delta);

    function change(uint256 x) external returns (uint256) {
        value = x;
        int256 wide = int256(x % 1000) - 500;
        int104 narrow = int104(wide * 3);
        int256 negated = -wide;
        last = wide;
        emit Signed(msg.sender, wide, narrow);
        emit SignedTopic(int24(wide), negated);
        return value;
    }

    function fail() external view {
        require(value <= 15, "range");
    }

    function read() external view returns (uint256) {
        return value + uint256(last > 0 ? last : -last);
    }
}
