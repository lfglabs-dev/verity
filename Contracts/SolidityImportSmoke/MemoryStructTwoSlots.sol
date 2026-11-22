// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// A flat memory struct lowers to one local per member whatever else the contract declares
// (#2830): as a multi-return helper result (named or returned in a tuple), as a component of
// a tuple declaration, and as an uninitialized local. The importer counts state variables
// across the whole compiled source, so each contract of the pair is alone in its file; they
// differ only by one unrelated state variable and one unused function.
contract MemoryStructTwoSlots {
    struct Pair {
        uint256 a;
        bool flag;
    }

    struct Span {
        uint256 lo;
        uint256 hi;
    }

    uint256 internal stored;
    uint256 internal unrelated;

    function unused() external view returns (uint256) {
        return unrelated;
    }

    function split(uint256 x) internal pure returns (Pair memory p, uint256 k) {
        p.a = x + 1;
        p.flag = x > 4;
        k = x * 2;
    }

    function make(uint256 x) internal pure returns (uint256 k, Pair memory) {
        if (x == 9) return (1, Pair(2, true));
        return (x + 3, Pair(x * 10, false));
    }

    function spans(uint256 x) internal pure returns (Span memory s, uint256 k, Span memory t) {
        s = Span(x, x + 1);
        k = x + 2;
        t = Span(x + 3, x + 4);
    }

    function named(uint256 x) external returns (uint256) {
        stored = x;
        (Pair memory p, uint256 k) = split(x);
        return p.flag ? p.a + k : p.a * 100 + k;
    }

    function tupled(uint256 x) external returns (uint256) {
        stored = x;
        (uint256 k, Pair memory p) = make(x);
        p.a += k;
        return p.flag ? p.a + 1000 : p.a;
    }

    function zeroed(uint256 x) external returns (uint256) {
        stored = x;
        Pair memory p;
        if (x > 3) {
            p.a = x;
            p.flag = true;
        }
        return p.flag ? p.a : p.a + 77;
    }

    // Later components start after every member of an earlier struct component.
    function ordered(uint256 x) external returns (uint256) {
        stored = x;
        (Span memory s, uint256 k, Span memory t) = spans(x);
        return s.lo + s.hi * 10 + k * 100 + t.lo * 1000 + t.hi * 10000;
    }
}
