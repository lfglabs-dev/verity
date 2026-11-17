// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract TerminalErrorGuard {
    error Rejected(uint256 supplied);

    function fail(uint256 supplied) external pure returns (uint256) {
        revert Rejected(supplied);
    }
}
