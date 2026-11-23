// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Modifiers whose `_;` sits in a branch or appears more than once (#2846). solc runs the
// remaining modifiers and the body at each `_;` it reaches: `twice` runs `gate` and the body
// twice, `gate` evaluates its argument at each entry (copy 2 sees `runs` + 100, which flips
// `x % 3`), `tally` is a single-`_;` modifier inside the chain, `split` runs the body in either
// branch with code before or after it, and `evenRuns` skips the body of `read`. Both copies write `total` and `tail`. The named return
// `out` starts at zero at each `_;` under via-IR, and is shared across the copies under legacy
// (`ModifierPlaceholderLegacySequence`).
contract SequenceFixture {
    uint256 private total;
    uint256 private runs;
    uint256 private skipped;
    uint256 private tail;

    modifier twice() {
        runs += 1;
        _;
        runs += 100;
        _;
        tail += runs;
    }

    modifier gate(uint256 x) {
        if (x % 3 != 1) {
            _;
        } else {
            skipped += x % 1000 + 1;
        }
    }

    modifier tally() {
        tail += tail % 7;
        _;
        skipped += tail % 5;
    }

    modifier split(uint256 x) {
        if (x % 2 == 0) {
            _;
            tail += 1;
        } else {
            tail += 10;
            _;
        }
    }

    modifier evenRuns() {
        if (runs % 2 == 0) _;
    }

    function change(uint256 input) external twice gate(input + runs) tally split(input) returns (uint256 out) {
        uint256 seed = input % 100000;
        uint256 local;
        local += seed + runs;
        total += local;
        out += total + tail + skipped;
        require(input != 20, "placeholder rollback");
    }

    function fail() external twice {
        total += 777;
        require(false, "forced revert");
    }

    function read() external view evenRuns returns (uint256) {
        return total + runs * 3 + skipped * 5 + tail * 7;
    }
}
