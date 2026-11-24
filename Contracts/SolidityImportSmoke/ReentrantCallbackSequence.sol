// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IHook {
    function hook() external;
}

/// A contract that a callee re-enters. `poke` and `tryPoke` write `pending`, then call the
/// target, which may call back into `enter`, `enterSmall` or `enterThenFail`. Each call is the
/// root's last state interaction, so the importer admits it (a trailing call). The callbacks
/// record their own sender and selector, count themselves in `callbacks` and copy what they
/// see of the caller's pre-call write, so a skipped callback, a wrong call context or a lost
/// rollback is a storage difference.
contract ReentrantCallbackFixture {
    uint256 private pending;
    uint256 private callbacks;
    address private lastSender;
    uint256 private lastSig;
    uint256 private seenPending;
    uint256 private lastSmall;

    error CallbackFailed(uint256 seen);

    function poke(address target, uint256 value) external {
        pending = value;
        IHook(target).hook();
    }

    function tryPoke(address target, uint256 value) external {
        pending = value;
        try IHook(target).hook() {} catch {}
    }

    function enter() external {
        callbacks += 1;
        lastSender = msg.sender;
        lastSig = uint256(uint32(msg.sig));
        seenPending = pending;
    }

    function enterSmall(uint8 value) external {
        callbacks += 1;
        lastSmall = value;
    }

    function enterThenFail() external {
        callbacks += 1;
        lastSender = msg.sender;
        uint256 seen = pending;
        revert CallbackFailed(seen);
    }
}
