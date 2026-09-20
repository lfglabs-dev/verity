// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

error NotOwner();
error EnforcedPause();
error ReentrancyGuardReentrantCall();

abstract contract OwnableLike {
    address public owner;

    modifier onlyOwner() {
        if (msg.sender != owner) revert NotOwner();
        _;
    }
}

abstract contract PausableLike {
    uint256 public paused;

    modifier whenNotPaused() {
        if (0 < paused) revert EnforcedPause();
        _;
    }
}

abstract contract ReentrancyGuardLike {
    uint256 public status;

    modifier nonReentrant() {
        if (1 < status) revert ReentrancyGuardReentrantCall();
        status = 2;
        _;
        status = 1;
    }
}

contract Child is OwnableLike, PausableLike, ReentrancyGuardLike {
    uint256 public value;

    function setOwner(address next) external {
        owner = next;
    }

    function arm() external {
        status = 1;
    }

    function guarded(uint256 amount) external onlyOwner whenNotPaused {
        value = amount;
    }

    function enter(uint256 amount) external nonReentrant returns (uint256) {
        value = amount;
        return amount;
    }

    function early(uint256 amount) external nonReentrant returns (uint256) {
        value = amount;
        return amount;
    }
}
