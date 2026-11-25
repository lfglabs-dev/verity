// SPDX-License-Identifier: MIT
pragma solidity 0.8.10;

// A stateful helper call as the right operand of `+` beside a `constant` or `immutable` state
// variable identifier. change(x) selects a case by x % 2 and drives it with y = x / 2: `bump`
// writes `stored` and returns it. Large inputs overflow the checked addition (Panic 0x11).
// This is `StatefulCallConstantOperandSequence` under solc 0.8.10, compiled with the legacy
// pipeline.
contract SequenceFixture {
    uint256 constant OFFSET = 3;
    uint256 immutable base = 5;

    uint256 stored;

    function bump(uint256 by) internal returns (uint256) {
        stored = stored + by;
        return stored;
    }

    function change(uint256 x) external {
        uint256 y = x / 2;
        uint256 r;
        if (x % 2 == 0) {
            r = OFFSET + bump(y);
        } else {
            r = base + bump(y);
        }
        stored = r;
    }

    function fail() external {
        stored = 99;
        require(stored < 1, "rollback void write");
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
