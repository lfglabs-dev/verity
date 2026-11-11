// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    uint256 private last;
    function bump(uint256[4] memory st) internal pure {
        for (uint256 i = 0; i < 4; i++) {
            st[i] = st[i] ^ (i + 1);
        }
    }
    function rotate(uint256[4] memory st) internal pure {
        uint256 t = st[0];
        st[0] = st[1];
        st[1] = st[2];
        st[2] = st[3];
        st[3] = t;
    }
    function spread(uint256 x) internal pure returns (uint256[4] memory words) {
        words[0] = x & 0xff;
        words[1] = (x >> 8) & 0xff;
        words[2] = (x >> 16) & 0xff;
        words[3] = (x >> 24) & 0xff;
    }
    function pick(uint256[4] memory st, uint256 k) internal pure returns (uint256[4] memory) {
        uint256[4] memory shifted;
        for (uint256 i = 0; i < 4; i++) {
            shifted[i] = st[(i + k) % 4];
        }
        if (k == 3) {
            return st;
        }
        return shifted;
    }
    function change(uint256 x) external returns (uint256) {
        uint256[4] memory st = spread(x);
        bump(st);
        rotate(st);
        uint256[4] memory picked = pick(st, x % 4);
        picked[x % 4] += 7;
        uint8[3] memory narrow;
        narrow[x % 3] = uint8(x >> 32);
        narrow[2] ^= 0x5a;
        value = st[0] + st[1] * 3 + st[2] * 5 + st[3] * 7 + picked[0] * 11 + picked[3] * 13
            + uint256(narrow[0]) + uint256(narrow[2]) * 17 + st.length;
        if (x % 7 == 6) {
            value += st[x % 6];
        }
        last = picked[(x >> 40) % 4];
        return value;
    }
    function rotateFixed(uint256[4] memory st, uint64[2] memory caps) external returns (uint256[4] memory) {
        bump(st);
        st[0] += caps[0];
        st[3] ^= caps[1];
        rotate(st);
        last = st[caps[1] % 4] + caps.length;
        return pick(st, caps[0] % 4);
    }
    function fail() external {
        uint256[2] memory probe;
        probe[0] = value;
        value = probe[value % 2 + 2];
    }
    function read() external view returns (uint256, uint256) {
        return (value, last);
    }
}
