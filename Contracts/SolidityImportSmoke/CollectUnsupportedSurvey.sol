// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
interface ISurveyCallee {
    function ping() external returns (uint256);
}
// Unsupported constructs for the `collectUnsupported` survey: a do-while loop,
// `gasleft()` in an inlined helper, `block.prevrandao`, the Yul builtin `gas()`
// and try/catch. `scaled` reads a local whose declaration is skipped.
contract CollectUnsupportedSurvey {
    uint256 private total;
    function scaled(uint256 x) internal view returns (uint256) {
        uint256 budget = gasleft();
        return x + budget;
    }
    function first(uint256 x) external returns (uint256) {
        uint256 y = x + 1;
        do { y += 1; } while (y < 10);
        total = scaled(y);
        total += block.prevrandao;
        return total;
    }
    function second(uint256 x, address callee) external returns (uint256 r) {
        assembly { r := gas() }
        try ISurveyCallee(callee).ping() returns (uint256 v) { r = v; } catch { r = 0; }
        r = r + x;
    }
    function read() external view returns (uint256) {
        return total;
    }
}
