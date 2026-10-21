// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

type Currency is address;
type PoolId is bytes32;
type BalanceDelta is int256;

function equalsCurrency(Currency a, Currency b) pure returns (bool) {
    return Currency.unwrap(a) == Currency.unwrap(b);
}

using {equalsCurrency as ==} for Currency global;

function toBalanceDelta(int128 _amount0, int128 _amount1) pure returns (BalanceDelta balanceDelta) {
    assembly ("memory-safe") {
        balanceDelta := or(shl(128, _amount0), and(sub(shl(128, 1), 1), _amount1))
    }
}

function addDelta(BalanceDelta a, BalanceDelta b) pure returns (BalanceDelta) {
    int256 res0;
    int256 res1;
    assembly ("memory-safe") {
        let a0 := sar(128, a)
        let a1 := signextend(15, a)
        let b0 := sar(128, b)
        let b1 := signextend(15, b)
        res0 := add(a0, b0)
        res1 := add(a1, b1)
    }
    return toBalanceDelta(int128(res0), int128(res1));
}

function subDelta(BalanceDelta a, BalanceDelta b) pure returns (BalanceDelta) {
    int256 res0;
    int256 res1;
    assembly ("memory-safe") {
        let a0 := sar(128, a)
        let a1 := signextend(15, a)
        let b0 := sar(128, b)
        let b1 := signextend(15, b)
        res0 := sub(a0, b0)
        res1 := sub(a1, b1)
    }
    return toBalanceDelta(int128(res0), int128(res1));
}

function eqDelta(BalanceDelta a, BalanceDelta b) pure returns (bool) {
    return BalanceDelta.unwrap(a) == BalanceDelta.unwrap(b);
}

function neqDelta(BalanceDelta a, BalanceDelta b) pure returns (bool) {
    return BalanceDelta.unwrap(a) != BalanceDelta.unwrap(b);
}

using {addDelta as +, subDelta as -, eqDelta as ==, neqDelta as !=} for BalanceDelta global;

library BalanceDeltaSlice {
    function amount0(BalanceDelta balanceDelta) internal pure returns (int128 _amount0) {
        assembly ("memory-safe") {
            _amount0 := sar(128, balanceDelta)
        }
    }

    function amount1(BalanceDelta balanceDelta) internal pure returns (int128 _amount1) {
        assembly ("memory-safe") {
            _amount1 := signextend(15, balanceDelta)
        }
    }
}

using BalanceDeltaSlice for BalanceDelta;

library CustomRevertSlice {
    function revertWith(bytes4 selector) internal pure {
        assembly ("memory-safe") {
            mstore(0, selector)
            revert(0, 0x04)
        }
    }

    function revertWith(bytes4 selector, uint24 value) internal pure {
        assembly ("memory-safe") {
            mstore(0, selector)
            mstore(4, and(value, 0xffffff))
            revert(0, 0x24)
        }
    }
}

struct PoolKey {
    Currency currency0;
    Currency currency1;
    uint24 fee;
    int24 tickSpacing;
    address hooks;
}

library PoolIdSlice {
    function toId(PoolKey memory poolKey) internal pure returns (PoolId poolId) {
        assembly ("memory-safe") {
            poolId := keccak256(poolKey, 0xa0)
        }
    }
}

library PositionSlice {
    function calculatePositionKey(address owner, int24 tickLower, int24 tickUpper, bytes32 salt)
        internal
        pure
        returns (bytes32 positionKey)
    {
        assembly ("memory-safe") {
            let fmp := mload(0x40)
            mstore(add(fmp, 0x26), salt)
            mstore(add(fmp, 0x06), tickUpper)
            mstore(add(fmp, 0x03), tickLower)
            mstore(fmp, owner)
            positionKey := keccak256(add(fmp, 0x0c), 0x3a)
            mstore(add(fmp, 0x40), 0)
        }
    }
}

abstract contract OwnedSlice {
    address public owner;

    modifier onlyOwner() virtual {
        require(msg.sender == owner, "UNAUTHORIZED");
        _;
    }
}

contract SequenceFixture is OwnedSlice {
    using CustomRevertSlice for bytes4;
    using PoolIdSlice for PoolKey;

    error ManagerLocked();
    error LPFeeTooLarge(uint24 fee);
    error ClearExactAmountMismatch();

    uint256 private value;
    mapping(PoolId id => uint256 feeWord) public poolFees;
    mapping(bytes32 posKey => uint256 liquidity) public positions;

    function change(uint256 delta) external returns (uint256) {
        owner = msg.sender;
        value += delta;
        return value;
    }

    function fail() external view returns (uint256) {
        require(value > 1000, "SequenceFixture: value too small");
        return value;
    }

    function read() external view returns (uint256) {
        return value;
    }

    function supportsInterface(bytes4 interfaceId) external pure returns (bool) {
        return interfaceId == 0x01ffc9a7 || interfaceId == 0x0f632fb3;
    }

    function extsload(bytes32 slot) external view returns (bytes32) {
        assembly ("memory-safe") {
            mstore(0, sload(slot))
            return(0, 0x20)
        }
    }

    function exttload(bytes32 slot) external view returns (bytes32) {
        assembly ("memory-safe") {
            mstore(0, tload(slot))
            return(0, 0x20)
        }
    }

    function setPoolFee(PoolKey memory key, uint24 newFee) external onlyOwner returns (PoolId id) {
        if (newFee > 1000000) LPFeeTooLarge.selector.revertWith(newFee);
        id = key.toId();
        poolFees[id] = uint256(newFee) | (uint256(uint24(key.tickSpacing)) << 24);
    }

    function accountPoolBalanceDelta(PoolKey memory key, int128 d0, int128 d1) external returns (int128 out0, int128 out1) {
        BalanceDelta a = toBalanceDelta(d0, d1);
        BalanceDelta b = toBalanceDelta(int128(key.tickSpacing), -int128(key.tickSpacing));
        BalanceDelta c = a + b - b;
        if (c != a) ManagerLocked.selector.revertWith();
        bytes32 slot = PoolId.unwrap(key.toId());
        int256 packed = BalanceDelta.unwrap(c);
        assembly ("memory-safe") {
            tstore(slot, packed)
        }
        return (c.amount0(), c.amount1());
    }

    function recordPositionLiquidity(int24 tickLower, int24 tickUpper, bytes32 salt, uint256 liq)
        external
        returns (bytes32 posKey)
    {
        posKey = PositionSlice.calculatePositionKey(msg.sender, tickLower, tickUpper, salt);
        positions[posKey] = liq;
    }
}
