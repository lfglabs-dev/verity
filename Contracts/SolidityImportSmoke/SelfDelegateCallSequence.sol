// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Synthetic self-dispatch `address(this).delegatecall(...)` fixture for A/B/C differential
/// validation across source EVM, Denote (`imported-model-self-delegate-v1`) and compiled Yul.
/// Verifies storage updates across batch sub-calls, preservation of outer `msg.sender`,
/// return-bytes forwarding on single self-dispatch, and full revert-data bubbling (both
/// custom-error payloads and empty reverts) with rollback of earlier sub-call writes.
contract SelfDelegateCallFixture {
    uint256 private total;
    uint256 private calls;
    address private lastSender;

    error BadAmount(uint256 amount);

    function addAmount(uint256 amount) external returns (uint256) {
        if (amount == 0) revert BadAmount(amount);
        total += amount;
        calls += 1;
        lastSender = msg.sender;
        return total;
    }

    function failEmpty() external pure {
        assembly ("memory-safe") {
            revert(0, 0)
        }
    }

    function multicall(bytes[] calldata data) external returns (uint256 executed) {
        for (uint256 i = 0; i < data.length; i++) {
            (bool success, bytes memory result) = address(this).delegatecall(data[i]);
            if (!success) {
                assembly ("memory-safe") {
                    revert(add(result, 0x20), mload(result))
                }
            }
            executed += 1;
        }
    }

    function selfDispatchSingle(bytes calldata payload) external returns (bytes memory) {
        (bool success, bytes memory result) = address(this).delegatecall(payload);
        if (!success) {
            assembly ("memory-safe") {
                revert(add(result, 0x20), mload(result))
            }
        }
        return result;
    }

    function read() external view returns (uint256, uint256, address) {
        return (total, calls, lastSender);
    }
}
