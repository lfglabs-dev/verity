// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Inline-assembly assignments of possibly dirty words to `bool` and `address` locals and
// named results. solc keeps the dirty stack word and cleans it at every Solidity-level use
// (`iszero(iszero(w))` / `and(w, 2^160 - 1)`); the importer stores the cleaned word, and
// rejects any later raw Yul read of it (SyntheticNarrowYulChecks.lean).
contract SyntheticNarrowYul {
    bool private flag;
    address private owner;
    uint256 private hits;

    event Observed(bool flag, address owner);

    function boolResult(uint256 x) external pure returns (bool ok) {
        assembly { ok := x }
    }

    function addressResult(uint256 x) external pure returns (address a) {
        assembly { a := x }
    }

    function boolLocalBranch(uint256 x) external pure returns (uint256) {
        bool ok;
        assembly { ok := and(x, 0xff00) }
        if (ok) return 1;
        return 2;
    }

    function boolCompare(uint256 x, uint256 y) external pure returns (bool same, bool negated) {
        bool a;
        bool b;
        assembly {
            a := x
            b := y
        }
        same = a == b;
        negated = !a;
    }

    function addressCompare(uint256 x) external pure returns (bool same, uint160 raw) {
        address a;
        assembly { a := x }
        same = a == address(uint160(x));
        raw = uint160(a);
    }

    function storeDirty(uint256 x, uint256 y) external returns (bool, address) {
        bool ok;
        address a;
        assembly {
            ok := x
            a := y
        }
        flag = ok;
        owner = a;
        emit Observed(ok, a);
        return (flag, owner);
    }

    function _successOf(uint256 w) private pure returns (bool success) {
        assembly { success := w }
    }

    function helperNamedBool(uint256 x) external returns (uint256) {
        bool success = _successOf(x);
        if (success) hits = hits + 1;
        return success ? 7 : 9;
    }

    function copiedBool(uint256 x) external pure returns (bool) {
        bool ok;
        assembly { ok := x }
        bool copy = ok;
        return copy;
    }
}

// Raw Yul reads of a cleaned narrow local are rejected: the source would observe the dirty word.
contract SyntheticNarrowYulUnsupported {
    function readBack(uint256 x) external pure returns (uint256 raw) {
        bool ok;
        assembly {
            ok := x
            raw := ok
        }
    }

    function readCopyLater(uint256 x) external pure returns (uint256 raw) {
        address a;
        assembly { a := x }
        address copy = a;
        assembly { raw := copy }
    }

    function _rawOf(bool b) private pure returns (uint256 raw) {
        assembly { raw := b }
    }

    function readThroughHelper(uint256 x) external pure returns (uint256) {
        bool ok;
        assembly { ok := x }
        return _rawOf(ok);
    }

    function readInLoop(uint256 x) external pure returns (uint256 raw) {
        bool ok;
        for (uint256 i = 0; i < 2; ++i) {
            assembly {
                raw := add(raw, ok)
                ok := x
            }
        }
    }
}
