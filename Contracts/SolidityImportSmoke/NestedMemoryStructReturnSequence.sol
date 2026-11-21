// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    struct Config {
        uint256 data;
    }
    struct Pair { uint256 a; uint256 b; uint8 tag; }
    struct Box { Pair pair; }
    struct Reserve {
        Config configuration;
        uint128 index;
        address token;
        Config extra;
    }
    uint256 private value;
    uint256 private last;
    function weight(Reserve memory r) internal pure returns (uint256) {
        return r.configuration.data % 1000 + r.extra.data * 3 + r.index;
    }
    function change(uint256 x) external returns (uint256) {
        Reserve memory r = Reserve(Config(x % 4096), uint128(x >> 128), address(0), Config(x % 5));
        value = weight(r) + x % 1000;
        last = x % 7;
        return value;
    }
    function fail() external {
        uint128 narrow = uint128(value);
        value = narrow + type(uint128).max;
    }
    function read() external view returns (Reserve memory res) {
        res.index = uint128(last);
        res.configuration.data = value;
        res.extra = Config(value % 97 + last);
        if (value % 3 == 1) {
            res.token = address(this);
        }
        if (value % 5 == 2) {
            delete res.configuration;
        }
        if (last == 3) {
            res = Reserve({configuration: Config(1), index: 2, token: address(0), extra: Config(value)});
        }
    }
    function snapshot(uint256 k) external view returns (Reserve memory) {
        uint8 dirty = 0;
        assembly { dirty := 257 }
        Box memory box = Box(Pair(value + k % 1000, last, 0));
        (box.pair.tag, box.pair.a) = (dirty, box.pair.a);
        box.pair.tag += dirty;
        uint8 tagCopy = box.pair.tag;
        uint256 rawTag = 0;
        assembly { rawTag := tagCopy }
        box.pair = Pair(box.pair.b, box.pair.a + rawTag, box.pair.tag);
        return Reserve(Config(box.pair.a), uint128(k), address(0), Config(box.pair.b));
    }
}
