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
    function advance(uint256[3] memory a) internal pure returns (uint256) {
        a[1] = (a[1] + 1) % 3;
        return a[1] + 40;
    }
    function reseat(uint256[3] memory a, uint256 v) internal pure returns (uint256) {
        a[0] = v;
        uint256[3] memory blank;
        a = blank;
        a[0] = 99;
        return a[0];
    }
    function scaled(uint256[3] memory a) internal pure returns (uint256[3] memory out) {
        out[0] = advance(a);
        out[1] = a[1];
        out[2] = a[0] ^ out[0];
        return out;
    }
    function sumScaled(uint256[3] memory a) internal pure returns (uint256) {
        uint256[3] memory s = scaled(a);
        return s[0] + s[1] + s[2];
    }
    function rebind(uint256 x) internal pure returns (uint256 acc) {
        uint256[3] memory idx;
        idx[1] = x % 3;
        idx[idx[1]] = advance(idx);
        uint256[3] memory same = idx;
        same[2] += 5;
        acc = idx[2] + idx[0] * 3 + idx[1] * 7;
        uint256[3] memory other;
        other[0] = x & 0xffff;
        same = other;
        same[1] = 9;
        acc += other[1] + idx[1];
        uint256 r = reseat(other, (x >> 16) & 0xffff);
        acc += r + other[0];
        delete other[0];
        acc += other[0] + same[0];
        delete same;
        same[2] = 1;
        acc += other[2] + same[2] * 11;
        for (uint256 j = 0; j < 3; j++) {
            uint256[2] memory fresh;
            acc += fresh[0] + fresh[1];
            fresh[j % 2] = j + 1;
            acc += fresh[0] * 13;
        }
        uint256[3] memory sc = scaled(idx);
        acc += sumScaled(other);
        acc += sc[0] + sc[2] + idx[1];
        bool[2] memory flags;
        flags[x % 2] = true;
        if (flags[1]) {
            acc += 17;
        }
        address[2] memory who;
        who[0] = address(uint160(x));
        acc += (uint256(uint160(who[0])) & 0xff) + uint256(uint160(who[1]));
        int256[2] memory signedVals;
        signedVals[0] = int256(x % 100) - 50;
        signedVals[1] = signedVals[0] * 3;
        if (signedVals[1] < 0) {
            acc += 19;
        }
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
        value ^= rebind(x);
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
