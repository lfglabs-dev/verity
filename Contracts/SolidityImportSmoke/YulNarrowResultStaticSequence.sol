// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IYulNarrowResultQuery {
    function canCall(address caller, address target, bytes4 selector) external view returns (bool, uint32);
}

/// A library helper whose named `bool` and `uint32` results are written from the two scratch
/// words a `staticcall` returns into. The answering account is untrusted: its first word may be
/// any word (`2`, all ones), its answer short or empty, so the raw word decides which callers
/// pass; a delay that does not fit 32 bits becomes zero.
library YulNarrowResultStaticLib {
    function query(address account, address caller, address target, bytes4 selector)
        internal view returns (bool immediate, uint32 delay)
    {
        bytes memory data = abi.encodeCall(IYulNarrowResultQuery.canCall, (caller, target, selector));
        assembly ("memory-safe") {
            mstore(0x00, 0x00)
            mstore(0x20, 0x00)
            if staticcall(gas(), account, add(data, 0x20), mload(data), 0x00, 0x40) {
                immediate := mload(0x00)
                delay := mload(0x20)
                delay := mul(delay, iszero(shr(32, delay)))
            }
        }
    }
}

contract YulNarrowResultStaticFixture {
    uint256 private stored;

    error Denied(address caller, uint32 delay);

    function peek(address account, bytes4 selector) external view returns (bool, uint32) {
        return YulNarrowResultStaticLib.query(account, msg.sender, address(this), selector);
    }

    function peekRaw(address account, bytes4 selector) external view returns (uint256 r, uint256 d) {
        (bool immediate, uint32 delay) = YulNarrowResultStaticLib.query(account, msg.sender, address(this), selector);
        assembly ("memory-safe") {
            r := immediate
            d := delay
        }
    }

    function guarded(address account, bytes4 selector, uint256 x) external {
        (bool immediate, uint32 delay) = YulNarrowResultStaticLib.query(account, msg.sender, address(this), selector);
        if (!immediate || delay != 0) revert Denied(msg.sender, delay);
        stored = x;
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
