// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    struct StaticCfg {
        uint128 scale;
        uint64 bonus;
        bool active;
    }

    struct Step {
        uint256 delta;
        uint64 weight;
        bool enabled;
    }

    struct Bundle {
        uint256 baseScore;
        Step[] steps;
        uint256[] bonuses;
    }

    error InvalidStep(uint256 index, uint256 delta);
    event BundleProcessed(uint256 indexed score, uint256 bitMetrics, bytes32 digest);

    uint256 private totalScore;
    uint256 private lastBitMetrics;
    bytes32 private lastDigest;

    function _msb(uint256 x) internal pure returns (uint8 r) {
        assembly ("memory-safe") {
            r := sub(255, clz(x))
        }
    }

    function _rawClz(uint256 x) internal pure returns (uint256 z) {
        assembly ("memory-safe") {
            z := clz(x)
        }
    }

    function _clearBit(uint256 bitmap, uint8 index) internal pure returns (uint256) {
        return bitmap & ~(1 << index);
    }

    function _log2Halving(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        uint256 v = value;
        uint256 bit = 128;
        unchecked {
            while (bit > 0) {
                if (v >= (1 << bit)) {
                    v >>= bit;
                    result += bit;
                }
                bit >>= 1;
            }
        }
        return result;
    }

    function _popCount(uint256 x) internal pure returns (uint256 count) {
        uint256 v = x;
        unchecked {
            while (v != 0) {
                count += 1;
                v &= (v - 1);
            }
        }
    }

    function _sumSetBits(uint256 bitmap) internal pure returns (uint256 acc) {
        uint256 pending = bitmap;
        while (pending != 0) {
            uint8 i = _msb(pending);
            acc += uint256(i) + 1;
            pending = _clearBit(pending, i);
        }
    }

    function _evalStaticMemory(StaticCfg memory cfg, uint256 x) internal pure returns (uint256) {
        if (!cfg.active) {
            return x;
        }
        return x * uint256(cfg.scale) + uint256(cfg.bonus);
    }

    function _evalBundleMemory(Bundle memory b, uint256 idx) internal pure returns (uint256, bytes32) {
        Bundle memory aliasB = b;
        uint256 acc = aliasB.baseScore;
        if (idx < aliasB.steps.length) {
            Step memory s = aliasB.steps[idx];
            if (s.enabled) {
                acc += s.delta * uint256(s.weight);
            }
        }
        if (idx < aliasB.bonuses.length) {
            acc += aliasB.bonuses[idx];
        }
        return (acc, keccak256(abi.encode(aliasB)));
    }

    function inspectStatic(StaticCfg calldata cfg, uint256 x) external pure returns (uint256) {
        StaticCfg calldata cdAlias = cfg;
        StaticCfg memory memCopy = cdAlias;
        return _evalStaticMemory(cfg, x) + (memCopy.active ? uint256(memCopy.bonus) : 0);
    }

    function applyBundle(Bundle calldata bundle, uint256 pivot) external returns (uint256, bytes32) {
        uint256 n = bundle.steps.length;
        uint256 acc = bundle.baseScore;
        if (n > 0) {
            uint256 lastIdx = n - 1;
            Step calldata cdLast = bundle.steps[n - 1];
            Step memory memFirst = bundle.steps[lastIdx - lastIdx];
            if (cdLast.enabled) {
                acc += cdLast.delta + uint256(cdLast.weight);
            }
            if (memFirst.enabled) {
                acc += memFirst.delta;
            }
        }
        (uint256 helperScore, bytes32 digest) = _evalBundleMemory(bundle, pivot);
        uint256 clzMetric = pivot == 0 ? _rawClz(0) : uint256(_msb(pivot));
        uint256 halvingMetric = _log2Halving(pivot == 0 ? 1 : pivot);
        uint256 popMetric = _popCount(pivot);
        uint256 msbSumMetric = _sumSetBits(pivot);
        uint256 metrics = clzMetric + halvingMetric * 1000 + popMetric * 1000000 + msbSumMetric * 100;
        totalScore += acc + helperScore;
        lastBitMetrics = metrics;
        lastDigest = digest;
        emit BundleProcessed(totalScore, lastBitMetrics, digest);
        return (totalScore, digest);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 z0 = _rawClz(0);
        if (input == 21) {
            revert InvalidStep(input, z0);
        }
        uint256 nonzero = input == 0 ? 1 : input;
        uint256 l2a = uint256(_msb(nonzero));
        uint256 l2b = _log2Halving(nonzero);
        require(l2a == l2b, "clz halving mismatch");
        uint256 pc = _popCount(input);
        uint256 sb = _sumSetBits(input);
        uint256 delta = z0 + l2a * 10 + pc * 100 + sb * 1000;
        totalScore += delta;
        lastBitMetrics = (pc << 16) | (sb << 8) | l2a;
        require(input != 20, "while clz rollback");
        return totalScore;
    }

    function fail() external {
        totalScore += 777;
        uint256 z1 = _rawClz(1);
        revert InvalidStep(99, z1);
    }

    function read() external view returns (uint256, uint256, bytes32) {
        return (totalScore, lastBitMetrics, lastDigest);
    }
}
