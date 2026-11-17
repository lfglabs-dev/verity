// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IScalarToken {
    function totalSupply() external view returns (uint256);
}

/// Immutables of each value-type family. The constructor writes the first seven, one of
/// them conditionally, so the source does not determine them: their values are the
/// constructor's arguments. `deployer` and `CHAIN` have inline initializers that read the
/// deployment environment; `SCALE` has a literal initializer and `UNSET` is never written.
contract SequenceFixture {
    uint256 private immutable START;
    uint64 private immutable DURATION;
    uint8 private immutable DECIMALS;
    bool private immutable ENABLED;
    bytes32 private immutable SALT;
    IScalarToken public immutable asset;
    int16 private immutable OFFSET;
    address public immutable deployer = msg.sender;
    uint256 private immutable CHAIN = block.chainid;
    uint256 private immutable SCALE = 1e6;
    uint256 private immutable UNSET;

    uint256 private value;

    error Disabled(uint256 start);

    constructor(
        uint256 start_, uint64 duration_, uint8 decimals_, bool enabled_, bytes32 salt_,
        IScalarToken asset_, int16 offset_
    ) {
        START = start_;
        DURATION = duration_;
        if (decimals_ > 18) {
            DECIMALS = 18;
        } else {
            DECIMALS = decimals_;
        }
        ENABLED = enabled_;
        SALT = salt_;
        asset = asset_;
        OFFSET = offset_;
    }

    function change(uint256 x) external returns (uint256) {
        require(ENABLED, Disabled(START));
        value = x;
        return x + START;
    }

    function fail() external view {
        require(value <= 15, "range");
        require(msg.sender == deployer, "deployer");
    }

    function read() external view returns (uint256) {
        return value;
    }

    function scalarWords()
        external
        view
        returns (uint256, uint64, uint8, bool, bytes32, address, int16, address, uint256, uint256, uint256)
    {
        return (START, DURATION, DECIMALS, ENABLED, SALT, address(asset), OFFSET, deployer, CHAIN,
            SCALE, UNSET);
    }

    function scaledEnd() external view returns (uint256) {
        return (START + uint256(DURATION)) * SCALE / (10 ** uint256(DECIMALS));
    }

    function isCurrentChain() external view returns (bool) {
        return block.chainid == CHAIN && SALT != bytes32(0);
    }
}
