// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    mapping(uint256 => uint256[7]) internal matrix;
    uint256 stamp;
    mapping(uint256 => uint16[7]) internal fees;
    event Ordered(uint256 trace, uint256 value);
    function first(uint256 x) internal returns (uint256) {
        stamp = stamp * 10 + 1;
        require(x < 30 || x == 40, "write key");
        return 1;
    }
    function second(uint256 x) internal returns (uint256) {
        stamp = stamp * 10 + 2;
        require(x < 40, "write index");
        return x % 9;
    }
    function right(uint256 x) internal returns (uint256) {
        stamp = stamp * 10 + 3;
        require(x < 20 || x == 30 || x == 40, "write RHS");
        return 42;
    }
    function change(uint256 x) external returns (uint256) {
        stamp = 0;
        matrix[first(x)][second(x)] = right(x);
        uint256 trace = stamp;
        uint256 selected = matrix[1][x % 9];
        emit Ordered(trace, selected);
        // Checked division must run before the LHS bounds test; its narrowed
        // value is captured before helper effects change stamp.
        fees[1][x % 7] = uint16(stamp / (x + 1));
        uint256 fee = fees[1][x % 7];
        return trace + fee;
    }
    function fail() external {
        stamp = 123;
        require(false, "write order rollback");
    }
    function read() external view returns (uint256) { return stamp; }
}
