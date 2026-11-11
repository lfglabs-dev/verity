// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    int256 private value;
    int256 private constant ALPHA = 523776;
    function centered(int256 r) internal pure returns (int256 r1, int256 r0) {
        r0 = r % ALPHA;
        if (r0 > ALPHA / 2) r0 -= ALPHA;
        r1 = (r - r0) / ALPHA;
    }
    function change(uint256 x) external returns (int256) {
        (int256 high, int256 low) = centered(int256(x % 8380417));
        int256 negative = -int256(x % 1000) % 7;
        int256 negativeDivisor = int256(x % 1000) % -7;
        int8 narrow = int8(int256(x % 256) - 128) % int8(-5);
        int256 minimum = (type(int256).min + int256(x % 2)) % -1;
        int256 folded = int256(x % 97) - 48;
        folded %= 5;
        int256 wrapped;
        unchecked { wrapped = (int256(x % 89) - 44) % 9; }
        value = high * 1000000 + low + negative + negativeDivisor + int256(narrow) + minimum + folded + wrapped;
        return value;
    }
    function fail() external view {
        require(value % (value - value) == 1, "unreachable");
    }
    function read() external view returns (int256) { return value; }
}
