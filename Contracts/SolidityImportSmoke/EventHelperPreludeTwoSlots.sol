// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Event arguments whose inlined helper reassigns its own result, parameter or local.
// EventHelperPreludeTwoSlots.sol is the same contract plus one unrelated state variable and
// one unused function. The importer lowers them the same way whatever the state-variable
// count (#2830).
contract EventHelperPreludeTwoSlots {
    mapping(uint256 => mapping(uint256 => uint256)) private nested;
    uint256 private unrelated;

    event Pair(uint256 indexed a, uint256 indexed b);
    event Mixed(uint256 indexed a, uint256 b, uint256 c);

    function mix(uint256 a) internal pure returns (uint256 r) {
        r = a;
        r = r ^ 0x55;
    }

    function rewrite(uint256 a) internal pure returns (uint256) {
        a = a | 0x100;
        return a;
    }

    function stored(uint256 a) internal view returns (uint256 r) {
        r = nested[a][1];
        r = r ^ a;
    }

    function nonzero(uint256 a) internal pure returns (uint256 r) {
        r = a;
        require(r != 0);
        r = r ^ 1;
    }

    function assembled(uint256 a) internal pure returns (uint256 r) {
        assembly {
            r := a
            r := xor(r, 7)
        }
    }

    function seed(uint256 k, uint256 v) external {
        nested[k][1] = v;
    }

    function helperTwice(uint256 x, uint256 y) external {
        emit Pair(mix(x), mix(y));
    }

    function helperAndLocal(uint256 x) external {
        uint256 k = x;
        emit Pair(k, rewrite(k));
    }

    function storedPair(uint256 x, uint256 y) external {
        emit Pair(stored(x), stored(y));
    }

    function guardedPair(uint256 x, uint256 y) external {
        emit Pair(nonzero(x), nonzero(y));
    }

    function assembledMixed(uint256 x, uint256 y) external {
        emit Mixed(assembled(x), mix(y), rewrite(x));
    }

    function unused() external {
        unrelated = 1;
    }
}
