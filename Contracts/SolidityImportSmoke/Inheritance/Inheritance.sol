// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

/// Synthetic Storage-like / Pausable-like / Ownable-like bases plus a diamond,
/// used as the S1 inheritance smoke. Only POC types plus `address` scalars.
abstract contract Base {
    uint256 public baseValue;

    function _bump() internal virtual {
        baseValue += 1;
    }
}

abstract contract Left is Base {
    uint256 public leftValue;
}

abstract contract Right is Base {
    uint256 public rightValue;
}

abstract contract PausableLike {
    uint256 public paused;

    function _pause() internal virtual {
        paused = 1;
    }

    function pause() external {
        _pause();
    }
}

abstract contract OwnableLike {
    address public owner;
}

contract Child is Left, Right, PausableLike, OwnableLike {
    uint256 public childValue;
    bytes32 private unusedGap;

    function _pause() internal virtual override {
        super._pause();
        childValue += 1;
    }

    function go() external {
        _pause();
    }

    function bump() external {
        _bump();
    }

    function _add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }
}
