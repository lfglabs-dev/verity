// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// A call to another contract's function that returns two words. There is no two-word
// external call lowering, so the call is a located rejection, whatever the number of
// state variables. It used to import as two calls that each decoded only word 0.
// The two contracts share this file on purpose: the old gate counted state variables
// across all compiled contracts, so it also fired for the one-variable contract.
contract ExternalTupleCall {
    uint256 private lo;
    uint256 private hi;
    function pair() external view returns (uint256, uint256) {
        return (lo, hi);
    }
    function change(uint256 x) external returns (uint256) {
        lo = x;
        hi = x ^ 1;
        (uint256 a, uint256 b) = ExternalTupleCall(address(this)).pair();
        return a ^ b;
    }
    function read() external view returns (uint256, uint256) {
        return (lo, hi);
    }
}

contract ExternalTupleCallSingleSlot {
    uint256 private lo;
    function pair() external view returns (uint256, uint256) {
        return (lo, lo + 1);
    }
    function change(uint256 x) external returns (uint256) {
        lo = x >> 1;
        (uint256 a, uint256 b) = ExternalTupleCallSingleSlot(address(this)).pair();
        return b - a;
    }
}
