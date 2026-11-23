// SPDX-License-Identifier: MIT
pragma solidity 0.8.10;

// A `T[] calldata` array with a narrow element type, copied to memory: returned as
// `T[] memory` (alone or in a tuple) and passed to a `T[] memory` helper. The legacy
// pipeline cleans each element of the copy (`uint8` 256 -> 0, `bool` 2 -> 1, `address`
// and `bytes4` masked); via-IR reverts with empty data. This is `CalldataNarrowArrayCopySequence`
// under solc 0.8.10, which the stateful harness compiles with the legacy pipeline (the 0.8.34
// fixture runs via-IR). solc 0.8.10 and 0.8.34 legacy copy these arrays the same way.
contract SequenceFixture {
    uint256 private total;
    uint256 private lastWeight;

    function change(uint256 x) external returns (uint256) {
        total = (total + x % 1000) % 1000003;
        return total;
    }

    function fail() external {
        total = 7;
        require(false, "fail");
    }

    function read() external view returns (uint256) {
        return total * 1000003 + lastWeight % 1000003;
    }

    function keepNarrow(uint8[] calldata xs) external returns (uint8[] memory) {
        record(weigh8(xs));
        return xs;
    }

    function keepWide(uint64[] calldata xs) external returns (uint256, uint64[] memory) {
        record(weigh64(xs));
        return (xs.length, xs);
    }

    function keepAddrs(address[] calldata xs) external returns (address[] memory) {
        record(weighAddrs(xs));
        return xs;
    }

    function keepFlags(bool[] calldata xs) external returns (bool[] memory, uint256) {
        record(weighFlags(xs));
        return (xs, xs.length);
    }

    function keepSelectors(bytes4[] calldata xs) external returns (bytes4[] memory) {
        record(weighSelectors(xs));
        return xs;
    }

    // One copy site each: only the memory-helper copy, only the root-result copy.
    function weighOnly(uint8[] calldata xs) external returns (uint256) {
        record(weigh8(xs));
        return lastWeight;
    }

    function passFlags(bool[] calldata xs) external returns (bool[] memory) {
        total = (total + xs.length) % 1000003;
        return xs;
    }

    function record(uint256 w) private {
        lastWeight = w;
        total = (total + w) % 1000003;
    }

    function weigh8(uint8[] memory a) private pure returns (uint256 s) {
        for (uint256 i = 0; i < a.length; i++) s += uint256(a[i]) * (i + 1);
    }

    function weigh64(uint64[] memory a) private pure returns (uint256 s) {
        for (uint256 i = 0; i < a.length; i++) s += uint256(a[i]) * (i + 1);
    }

    function weighAddrs(address[] memory a) private pure returns (uint256 s) {
        for (uint256 i = 0; i < a.length; i++) s += uint256(uint160(a[i])) % 1000003 + i;
    }

    function weighFlags(bool[] memory a) private pure returns (uint256 s) {
        for (uint256 i = 0; i < a.length; i++) if (a[i]) s += i + 1;
    }

    function weighSelectors(bytes4[] memory a) private pure returns (uint256 s) {
        for (uint256 i = 0; i < a.length; i++) s += uint256(uint32(a[i])) % 1000003 + i;
    }
}
