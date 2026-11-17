// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Root-level cases for the `collectUnsupported` survey: two overloads of
// `pick` (one with an unsupported body), and roots whose parameter or return
// type is unsupported, so lowering stops at the root boundary.
contract CollectUnsupportedRootBoundary {
    uint256 private total;
    function pick(uint256 x) external returns (uint256) {
        do { x += 1; } while (x < 10);
        total = x;
        return total;
    }
    function pick(address) external view returns (uint256) {
        return total;
    }
    function narrowKey(bytes2 key) external returns (uint256) {
        do { total += 1; } while (total < 10);
        return uint256(uint16(key));
    }
    function narrowResult(uint256 x) external returns (bytes2 r) {
        do { x += 1; } while (x < 10);
        total = x;
        r = bytes2(uint16(x));
    }
    function read() external view returns (uint256) {
        return total;
    }
}
