// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// A declaration in an `if` branch that falls through, inside an inlined helper whose other
// branch returns, goes out of scope at the end of the branch: inline assembly after the `if`
// reads the outer variable or constant of the same name (solc 0.8.34, both pipelines). The
// importer lowers the continuation inside the falling-through branch (and string and array
// helpers flatten a plain block into their continuation), so the end of the branch or block must
// restore the name-keyed Yul scope. The pair differs only by one unrelated state variable
// and one unused function (#2830 method; the constant counts as the one-slot contract's state
// variable); the bug itself does not depend on the state count.
contract HelperBranchScopeOneSlot {
    uint256 internal constant LIMIT = 11;

    function thenDeclares(uint256 c) internal pure returns (uint256 r) {
        uint256 v = 5;
        if (c > 0) { uint256 v = 7; v; } else { return 1; }
        assembly { r := v }
    }

    function elseDeclares(uint256 c) internal pure returns (uint256 r) {
        uint256 v = 5;
        if (c == 0) { return 1; } else { uint256 v = 7; v; }
        assembly { r := v }
    }

    function nestedDeclares(uint256 c) internal pure returns (uint256 r) {
        uint256 v = 5;
        if (c > 0) {
            if (c > 1) { uint256 v = 7; v; } else { return 2; }
        } else { return 1; }
        assembly { r := v }
    }

    function outerBranchDeclares(uint256 c) internal pure returns (uint256 r) {
        uint256 v = 5;
        if (c > 0) {
            uint256 v = 8;
            if (c > 1) { v = 9; } else { return 2; }
        } else { return 1; }
        assembly { r := v }
    }

    function shadowsConstant(uint256 c) internal pure returns (uint256 r) {
        if (c > 0) { uint256 LIMIT = 7; LIMIT; } else { return 1; }
        assembly { r := LIMIT }
    }

    function assignsOuter(uint256 c) internal pure returns (uint256 r) {
        uint256 v = 5;
        if (c > 0) { v = c + 20; } else { return 1; }
        assembly { r := v }
    }

    function uncheckedBranch(uint256 c) internal pure returns (uint256 r) {
        uint256 v = 5;
        if (c > 0) { unchecked { uint256 v = c - 1; v; } } else { return 1; }
        assembly { r := v }
    }

    function blockDeclaresString(uint256 c) internal pure returns (string memory) {
        uint256 v = 5;
        { uint256 v = c + 7; v; }
        uint256 w;
        assembly { w := v }
        if (w == 5) { return "five"; }
        return "other";
    }

    function blockDeclaresArray(uint256 c) internal pure returns (uint256[] memory) {
        uint256[] memory a = new uint256[](1);
        { uint256[] memory a = new uint256[](c + 3); a; }
        uint256[] memory r;
        assembly { r := a }
        return r;
    }

    function runThenDeclares(uint256 c) external pure returns (uint256) { return thenDeclares(c); }
    function runElseDeclares(uint256 c) external pure returns (uint256) { return elseDeclares(c); }
    function runNestedDeclares(uint256 c) external pure returns (uint256) { return nestedDeclares(c); }
    function runOuterBranchDeclares(uint256 c) external pure returns (uint256) {
        return outerBranchDeclares(c);
    }
    function runShadowsConstant(uint256 c) external pure returns (uint256) { return shadowsConstant(c); }
    function runAssignsOuter(uint256 c) external pure returns (uint256) { return assignsOuter(c); }
    function runUncheckedBranch(uint256 c) external pure returns (uint256) { return uncheckedBranch(c); }
    function runBlockDeclaresString(uint256 c) external pure returns (uint256) {
        return bytes(blockDeclaresString(c)).length;
    }
    function runBlockDeclaresArray(uint256 c) external pure returns (uint256) {
        uint256[] memory r = blockDeclaresArray(c);
        return r.length;
    }
}
