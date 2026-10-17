pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 total;
    mapping(uint256 => uint256) m;

    function change(uint256 value) external returns (uint256, uint256) {
        (uint128 a, , uint128 c) = split(value);
        uint256 t = value % 8 days;
        (uint256 start, uint256 end, uint256 lo, uint256 hi) =
            t < 1 days ? (0 days, 1 days, uint256(a) * 3, uint256(c)) :
            t < 7 days ? (1 days, 7 days, uint256(c), uint256(a) + (t - 1 days)) :
                         (7 days, 8 days, a, c);
        uint256 fee = (lo * (end - t) + hi * (t - start)) / (end - start);
        m[value % 4] = fee + a;
        (uint256 p, uint256 q) = pair(value % 1000);
        total = total % 10000 + p + q + c;
        return (fee, total);
    }

    function split(uint256 x) internal view returns (uint128, uint128, uint128) {
        if (x % 3 == 0) return (uint128(x % 1000), uint128(m[x % 4]), 1);
        uint128 base = uint128(total % 500);
        if (x % 3 == 1) {
            return (base, 2, uint128(x % 77));
        }
        return (uint128(m[x % 4] % 99), base + 1, base);
    }

    function pair(uint256 x) internal pure returns (uint256, uint256) {
        return (x, x + 1);
    }

    function fail() external returns (uint256) {
        total += 1;
        (uint256 u, uint256 v) = (total - 1000, 7 / (total % 3));
        return u + v;
    }

    function read() external view returns (uint256, uint256, uint256) {
        return triple(total);
    }

    function triple(uint256 x) internal view returns (uint256, uint256, uint256) {
        if (x % 2 == 0) {
            return (x, m[0], m[1]);
        } else {
            return (m[2], x + 1, m[3]);
        }
    }
}
