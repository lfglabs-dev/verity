// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    error GuardTriggered(uint256 seed, uint64 epoch);
    event GuardEvaluated(uint256 indexed seed, bool pausedAfter);

    bool private paused;
    uint64 private epochCount;
    bool private defaulted;
    uint256 private accumulator;

    function _emptyHook(uint256) internal pure returns (uint256) {}

    function _checkAndAdvance(uint256 seed) internal {
        uint64 currentEpoch = epochCount;
        if (seed == 19) {
            revert GuardTriggered(seed, currentEpoch);
        }
        if (paused) {
            if (!defaulted) {
                accumulator = accumulator + seed + 11;
                defaulted = true;
                return;
            }
        }
        epochCount = epochCount + 1;
        paused = !paused;
        defaulted = false;
        accumulator = accumulator + seed * 3 + 5;
        emit GuardEvaluated(seed, paused);
    }

    function change(uint256 input) external returns (uint256 out) {
        uint256 seed = input % 100000;
        _checkAndAdvance(seed);
        uint256 hookZero = _emptyHook(seed);
        out = accumulator + uint256(epochCount) * 100 + (paused ? 10 : 0) + (defaulted ? 1 : 0) + hookZero;
        if (input == 21) {
            return out + 77;
        }
        require(input != 20, "void helper guard rollback");
    }

    function fail() external {
        paused = true;
        accumulator = 999;
        require(false, "forced revert");
    }

    function read() external view returns (uint256 snapshot) {
        snapshot = accumulator + uint256(epochCount) * 100 + (paused ? 10 : 0) + (defaulted ? 1 : 0);
    }
}
