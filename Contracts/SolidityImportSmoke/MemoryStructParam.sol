// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// A memory struct is a reference: when a caller passes its own memory struct to an internal
// helper, a member write in the helper changes the caller's struct, and returning the parameter
// hands the caller its own struct back. The importer binds the parameter as a copy, so both are
// rejected with a location. The rule is conservative: a return is rejected even when the caller
// never writes either struct afterwards. Reads, writes to a struct built in the argument or copied
// from storage, and writes to the helper's own struct import (MemoryStructParamChecks.lean).
contract MemoryStructParam {
    struct P {
        uint256 a;
        uint256 b;
    }
    uint256 private total;
    uint256 private count;

    function setA(P memory p) internal pure returns (uint256) {
        p.a = 5;
        return 7;
    }
    function addA(P memory p) internal pure returns (uint256) {
        p.a += 1;
        return 7;
    }
    function incA(P memory p) internal pure returns (uint256) {
        p.a++;
        return 7;
    }
    function clearA(P memory p) internal pure returns (uint256) {
        delete p.a;
        return 7;
    }
    function forward(P memory p) internal pure returns (uint256) {
        uint256 r = setA(p);
        return r + 1;
    }
    function same(P memory p) internal pure returns (P memory) {
        return p;
    }
    function sameParen(P memory p) internal pure returns (P memory) {
        return (p);
    }
    function pick(P memory p, bool c) internal pure returns (P memory) {
        return c ? p : P(0, 0);
    }
    function pair(P memory p) internal pure returns (P memory, uint256) {
        return (p, 2);
    }
    function sum(P memory p) internal pure returns (uint256) {
        return p.a + p.b;
    }
    function fresh(uint256 v) internal pure returns (P memory) {
        P memory r = P(v, 1);
        r.b = v + 2;
        return r;
    }

    function writeDirect(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = setA(p);
        total = p.a + r;
        return total;
    }
    function writeCompound(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = addA(p);
        total = p.a + r;
        return total;
    }
    function writeIncrement(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = incA(p);
        total = p.a + r;
        return total;
    }
    function writeDelete(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = clearA(p);
        total = p.a + r;
        return total;
    }
    function writeNested(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = forward(p);
        total = p.a + r;
        return total;
    }
    function returnDirect(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        P memory q = same(p);
        q.a = 1;
        total = p.a + q.b;
        return total;
    }
    function returnParen(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        P memory q = sameParen(p);
        q.a = 1;
        total = p.a + q.b;
        return total;
    }
    function returnConditional(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        P memory q = pick(p, x > 3);
        q.a = 1;
        total = p.a + q.b;
        return total;
    }
    function returnTuple(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        (P memory q, uint256 k) = pair(p);
        q.a = 1;
        total = p.a + k;
        return total;
    }
    function readOnly(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        total = sum(p) + p.a;
        return total;
    }
    function writeTemporary(uint256 x) external returns (uint256) {
        total = setA(P(x, 4)) + x;
        return total;
    }
    function writeOwnStruct(uint256 x) external returns (uint256) {
        P memory q = fresh(x);
        count = q.a + q.b;
        return count;
    }

    // Added forms: tuple-assignment target, decrement, `using for` receiver, and a storage
    // argument (copied to memory by solc, so the helper's write is invisible: accepted).
    function tupleA(P memory p) internal pure returns (uint256) {
        uint256 k;
        (p.a, k) = (5, 1);
        return k;
    }
    function decA(P memory p) internal pure returns (uint256) {
        p.a--;
        return 7;
    }
    using MemoryStructParamLib for P;
    P private stored;
    function writeTuple(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = tupleA(p);
        total = p.a + r;
        return total;
    }
    function writeDecrement(uint256 x) external returns (uint256) {
        P memory p = P(x + 1, 4);
        uint256 r = decA(p);
        total = p.a + r;
        return total;
    }
    function writeReceiver(uint256 x) external returns (uint256) {
        P memory p = P(x, 4);
        uint256 r = p.bumpA();
        total = p.a + r;
        return total;
    }
    function writeStorageCopy(uint256 x) external returns (uint256) {
        stored.a = x;
        uint256 r = setA(stored);
        total = stored.a + r;
        return total;
    }
}

library MemoryStructParamLib {
    function bumpA(MemoryStructParam.P memory p) internal pure returns (uint256) {
        p.a = 1;
        return 2;
    }
}
