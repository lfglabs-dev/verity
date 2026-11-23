// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `try this.f(...)` must be handled the same way whatever else the contract declares (#2830).
// It is an external CALL to this contract: `f` runs in a new frame whose storage writes persist
// on success and roll back on failure, a `returns (...)` clause decodes its return data, and
// each `catch` clause selects on the revert data (`catch Error(string memory)` alone does not
// catch a revert without data). The importer does not model that call, so every form rejects at
// the `try`. Each contract of the pair is alone in its file; the pair differs only by one
// unrelated state variable and one unused function.
contract SelfTryCallOneSlot {
    uint256 internal stored;

    function target(uint256 a) external returns (uint256) {
        stored = a;
        if (a == 0) revert("zero");
        if (a == 1) revert();
        return a + 1;
    }

    function poke(uint256 a) external {
        stored = a;
        if (a == 0) revert("zero");
        if (a == 1) revert();
    }

    function guarded(uint256 a) internal {
        try this.poke(a) { } catch { revert("caught"); }
    }

    function catchAll(uint256 a) external returns (uint256 r) {
        try this.poke(a) { r = 1; } catch { r = 2; }
    }

    function errorOnly(uint256 a) external returns (uint256 r) {
        try this.poke(a) { r = 1; } catch Error(string memory) { r = 3; }
    }

    function returned(uint256 a) external returns (uint256 r) {
        try this.target(a) returns (uint256 v) { r = v; } catch { r = 2; }
    }

    function revertData(uint256 a) external returns (uint256 r) {
        try this.poke(a) { r = 1; } catch (bytes memory d) { r = 100 + d.length; }
    }

    function inHelper(uint256 a) external returns (uint256) {
        guarded(a);
        return 7;
    }
}
