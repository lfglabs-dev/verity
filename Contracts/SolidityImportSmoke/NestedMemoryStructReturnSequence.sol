// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    struct Inner {
        uint256 data;
    }
    struct Pair { uint256 a; uint256 b; uint8 tag; }
    struct Box { Pair pair; }
    struct Outer {
        Inner cfg;
        uint128 idx;
        address token;
        Inner spare;
    }
    uint256 private value;
    uint256 private last;
    function weight(Outer memory r) internal pure returns (uint256) {
        return r.cfg.data % 1000 + r.spare.data * 3 + r.idx;
    }
    function change(uint256 x) external returns (uint256) {
        Outer memory r = Outer(Inner(x % 4096), uint128(x >> 128), address(0), Inner(x % 5));
        value = weight(r) + x % 1000;
        last = x % 7;
        return value;
    }
    function fail() external {
        uint128 narrow = uint128(value);
        value = narrow + type(uint128).max;
    }
    function read() external view returns (Outer memory res) {
        res.idx = uint128(last);
        res.cfg.data = value;
        res.spare = Inner(value % 97 + last);
        if (value % 3 == 1) {
            res.token = address(this);
        }
        if (value % 5 == 2) {
            delete res.cfg;
        }
        if (last == 3) {
            res = Outer({cfg: Inner(1), idx: 2, token: address(0), spare: Inner(value)});
        }
    }
    function nestedOrder(uint256 x) external view returns (Outer memory) {
        uint256 k = x % 1000 + value;
        return Outer(Inner(k), uint128(++k), address(0), Inner(++k));
    }
    function snapshot(uint256 k) external view returns (Outer memory) {
        uint8 dirty = 0;
        assembly { dirty := 257 }
        Box memory box = Box(Pair(value + k % 1000, last, 0));
        (box.pair.tag, box.pair.a) = (dirty, box.pair.a);
        box.pair.tag += dirty;
        uint8 tagCopy = box.pair.tag;
        uint256 rawTag = 0;
        assembly { rawTag := tagCopy }
        box.pair = Pair(box.pair.b, box.pair.a + rawTag, box.pair.tag);
        return Outer(Inner(box.pair.a), uint128(k), address(0), Inner(box.pair.b));
    }
}
