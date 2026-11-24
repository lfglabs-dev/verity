// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// `abi.decode(data, (S))` of a flat static struct with `enum` members, from a `bytes memory`
/// buffer: as a struct local, as one component of a tuple, and with a narrow member next to the
/// enums. solc validates every member word: an enum word at or above its member count, a
/// `uint64` word above 64 bits and an `address` word above 160 bits revert with no data.
/// `change(x)` picks the shape by `x % 4`; `y = x >> 2` supplies the words.
contract SequenceFixture {
    enum Mode {
        Off,
        Slow,
        Fast
    }

    enum Tier {
        Low,
        Mid,
        High,
        Top,
        Max
    }

    struct Config {
        uint64 id;
        Mode mode;
        address oracle;
        Tier tier;
    }

    uint256 internal lastId;
    uint8 internal lastMode;
    uint8 internal lastTier;
    address internal lastOracle;
    uint256 internal fastCount;

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 4;
        uint256 y = x >> 2;
        // y = id | dirtyId << 64 | mode << 65 | tier << 68 | dirtyOracle << 71 | oracle << 72:
        // mode 3..7 and tier 5..7 are out of range, and a dirty bit sets bit 64 of the
        // `uint64` word or bit 160 of the `address` word.
        uint256 idWord = y & 0x1ffffffffffffffff;
        uint256 modeWord = (y >> 65) & 7;
        uint256 tierWord = (y >> 68) & 7;
        uint256 oracleWord = uint256(uint160(y >> 72)) | (((y >> 71) & 1) << 160);
        if (c == 0) {
            bytes memory data = abi.encode(idWord, modeWord, oracleWord, tierWord);
            Config memory cfg = abi.decode(data, (Config));
            lastId = cfg.id;
            lastMode = uint8(cfg.mode);
            lastOracle = cfg.oracle;
            lastTier = uint8(cfg.tier);
            if (cfg.mode == Mode.Fast) {
                fastCount += 1;
            }
            return uint256(cfg.tier) * 16 + uint256(cfg.mode);
        } else if (c == 1) {
            bytes memory data = abi.encode(idWord, modeWord, oracleWord, tierWord, y);
            (Config memory cfg, uint256 extra) = abi.decode(data, (Config, uint256));
            lastId = extra;
            lastTier = uint8(cfg.tier);
            return cfg.tier == Tier.Max ? 1 : uint256(cfg.mode) + 2;
        } else if (c == 2) {
            // The raw mode word straight from y: anything at or above 3 reverts.
            bytes memory data = abi.encode(uint256(7), y, uint256(0), uint256(0));
            Config memory cfg = abi.decode(data, (Config));
            lastMode = uint8(cfg.mode);
            return uint256(cfg.mode);
        } else {
            // Too short for the four head words: reverts before any member is read.
            bytes memory data = abi.encode(idWord, modeWord, oracleWord);
            Config memory cfg = abi.decode(data, (Config));
            return uint256(cfg.mode);
        }
    }

    function fail() external pure {
        revert();
    }

    function read() external view returns (uint256, uint8, uint8, address, uint256) {
        return (lastId, lastMode, lastTier, lastOracle, fastCount);
    }
}
