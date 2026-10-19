// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Events whose non-indexed data holds dynamic `T[] calldata` arrays: solc
/// copies full-word elements verbatim and validates every narrower element,
/// reverting with no data on a dirty word at the emit.
library BatchEvents {
    event Batch(address indexed caller, address[] accounts, uint256[] amounts, address indexed target);
}

contract DynamicAddressEventSequence {
    event Flags(uint256 indexed tag, bool[] flags, uint64 note, bytes32[] keys);
    event Narrow(uint8[] small, int256[] signed);

    error InconsistentInput();

    uint256 private total;

    function batch(address[] calldata accounts, uint256[] calldata amounts, address target) external {
        require(accounts.length == amounts.length, InconsistentInput());
        emit BatchEvents.Batch(msg.sender, accounts, amounts, target);
        total += accounts.length;
    }

    function batchThenCheck(address[] calldata accounts, uint256[] calldata amounts, address target)
        external
        returns (uint256)
    {
        emit BatchEvents.Batch(target, accounts, amounts, msg.sender);
        if (target == address(0)) revert InconsistentInput();
        return amounts.length;
    }

    function flags(uint256 tag, bool[] calldata values, uint64 note, bytes32[] calldata keys)
        external
        returns (uint256)
    {
        emit Flags(tag, values, note, keys);
        return values.length + keys.length;
    }

    function narrow(uint8[] calldata small, int256[] calldata signed) external {
        emit Narrow(small, signed);
        emit Narrow(small, signed);
    }

    function count() external view returns (uint256) {
        return total;
    }
}
