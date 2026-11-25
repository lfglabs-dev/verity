// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// A stateful helper call as the right operand of `+` beside a `constant` or `immutable` state
// variable identifier. change(x) selects a case by x % 2 and drives it with y = x / 2: `bump`
// writes `stored` and returns it. Large inputs overflow the checked addition (Panic 0x11).
// `StatefulCallConstantOperandSolc0810Sequence` is the same contract under solc 0.8.10, which
// the stateful harness compiles with the legacy pipeline; this one runs via-IR.
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
