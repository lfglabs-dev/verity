// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// `while (!cond)` has no iteration bound the importer can derive from the loop. It used to lower
// to a loop of at most 256 iterations when the sources declared more than one state variable,
// so `countTo(300)` stored 256 where solc stores 300. It is now a located rejection in every
// contract.
contract WhileNegatedCondition {
    uint256 private steps;
    uint256 private last;
    function countTo(uint256 n) external {
        uint256 i = 0;
        while (!(i == n)) {
            i = i + 1;
        }
        steps = i;
    }
    function countDown(uint256 n) external {
        uint256 i = n;
        while (!(i < 10)) {
            i = i - 10;
        }
        last = i;
    }
}
