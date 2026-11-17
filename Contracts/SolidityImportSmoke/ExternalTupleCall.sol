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

// The other two entry points of a two-word external call: a bare expression statement and
// partial destructuring. Both are located rejections too.
contract ExternalTupleCallStatement {
    uint256 private lo;
    function pair() external view returns (uint256, uint256) {
        return (lo, lo);
    }
    function poke() external view {
        ExternalTupleCallStatement(address(this)).pair();
    }
    function first() external view returns (uint256) {
        (uint256 a, ) = ExternalTupleCallStatement(address(this)).pair();
        return a;
    }
}

// Not external calls: `super.pair()` and `TuplePairBase.pair()` name an internal function
// of a base contract, so they are inlined, with two state variables as well.
contract TuplePairBase {
    uint256 internal lo;
    uint256 internal hi;
    function pair() internal view returns (uint256, uint256) {
        return (lo, hi);
    }
}

contract InternalTupleBaseCall is TuplePairBase {
    function change(uint256 x) external returns (uint256) {
        lo = x;
        hi = x >> 1;
        (uint256 a, uint256 b) = super.pair();
        (uint256 c, uint256 d) = TuplePairBase.pair();
        return a ^ (b << 1) ^ (c << 2) ^ (d << 3);
    }
    function read() external view returns (uint256, uint256) {
        (uint256 a, uint256 b) = TuplePairBase.pair();
        return (b, a);
    }
    function fail() external {
        lo = 7;
        revert();
    }
}
