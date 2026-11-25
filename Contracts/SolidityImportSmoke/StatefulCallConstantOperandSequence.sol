// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant FILE_OFFSET = 7;

// A stateful helper call as the right operand of `+` beside a contract or file-level `constant`
// or an `immutable` state variable identifier. change(x) selects a case by x % 3 and drives it
// with y = x / 3: `bump` writes `stored` and returns it. Large inputs overflow the checked
// addition (Panic 0x11). This is a value check: the importer counts three state variables here
// (file-level constants are not among them), so the one-versus-two count invariance of these
// shapes is checked by check_state_count_invariance instead.
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
        uint256 y = x / 3;
        uint256 r;
        uint256 c = x % 3;
        if (c == 0) {
            r = OFFSET + bump(y);
        } else if (c == 1) {
            r = base + bump(y);
        } else {
            r = FILE_OFFSET + bump(y);
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
