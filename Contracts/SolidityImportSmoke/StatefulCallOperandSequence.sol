// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library WordDoubling {
    function twice(uint256 v) internal pure returns (uint256) {
        return v * 2;
    }
}

// A stateful helper call as the right operand of `+` beside a local or parameter identifier,
// and as the lone argument (or using-for receiver) of a helper, in a contract with a single
// state variable. change(x) selects a case by x % 4 and drives it with y = x / 4: `bump` writes
// the state variable and returns it, `readPlus` reads it after its argument ran. Large inputs
// overflow the checked arithmetic (Panic 0x11) inside or after the call.
// `StatefulCallOperandSolc0810Sequence` is the same contract under solc 0.8.10, which the
// stateful harness compiles with the legacy pipeline; this one runs via-IR.
contract SequenceFixture {
    using WordDoubling for uint256;

    uint256 stored;

    function bump(uint256 by) internal returns (uint256) {
        stored = stored + by;
        return stored;
    }

    function readPlus(uint256 v) internal view returns (uint256) {
        return v * 1000 + stored;
    }

    function change(uint256 x) external {
        uint256 c = x % 4;
        uint256 y = x / 4;
        uint256 r;
        if (c == 0) {
            r = y + bump(1);
        } else if (c == 1) {
            r = x + bump(2);
        } else if (c == 2) {
            r = readPlus(bump(y));
        } else {
            r = bump(y).twice();
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
