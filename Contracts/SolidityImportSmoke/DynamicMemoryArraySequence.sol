// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    uint256 private last;
    uint256 private constant Q = 8380417;
    function add(uint256[] memory a, uint256[] memory b) internal pure returns (uint256[] memory c) {
        c = new uint256[](a.length);
        for (uint256 i = 0; i < a.length; i++) {
            c[i] = addmod(a[i], b[i], Q);
        }
    }
    function scaled(uint256[] memory a, uint256 s) internal pure returns (uint256[] memory) {
        uint256[] memory out = new uint256[](a.length);
        for (uint256 i = 0; i < a.length; i++) {
            out[i] = mulmod(a[i], s, Q);
        }
        if (s == 0) {
            return a;
        }
        return out;
    }
    function split(uint256[] memory a) internal pure returns (uint256[] memory head, uint256 total) {
        head = new uint256[](a.length > 2 ? 2 : a.length);
        for (uint256 i = 0; i < a.length; i++) {
            total += a[i];
            if (i < head.length) {
                head[i] = a[i];
            }
        }
    }
    function window(uint256[] memory a, uint256 k) internal pure returns (uint256[] memory, uint256) {
        if (k == 0 || a.length == 0) {
            return (a, a.length);
        }
        uint256[] memory w = new uint256[](k);
        for (uint256 i = 0; i < k; i++) {
            w[i] = a[i % a.length] + i;
        }
        return (w, k * 7);
    }
    function bumpAll(uint256[] memory a) internal pure {
        for (uint256 i = 0; i < a.length; i++) {
            a[i] += 1;
        }
    }
    function vecSum(uint256[][] memory v) internal pure returns (uint256 s) {
        for (uint256 i = 0; i < v.length; i++) {
            uint256[] memory row = v[i];
            for (uint256 j = 0; j < row.length; j++) {
                s += row[j] * (i + 1);
            }
        }
    }
    function same(uint256[] memory a) internal pure returns (uint256[] memory) {
        return a;
    }
    function clear(uint256[] memory a) internal pure {
        delete a;
    }
    function rebind(uint256[] memory a, uint256[] memory b) internal pure returns (uint256) {
        a[0] += 2;
        a = b;
        a[0] += 5;
        a = new uint256[](3);
        a[1] = 4;
        return a.length + a[1];
    }
    function owners(uint256 x) internal pure returns (uint256 r) {
        uint256[] memory e;
        e = new uint256[](x % 3 + 1);
        uint256[] memory f = same(e);
        uint256[] memory q = new uint256[](2);
        r = rebind(e, q);
        f[0] += 1;
        clear(e);
        r += e.length * 10 + e[0] * 20;
        e = new uint256[](x % 4 + 2);
        r += f.length * 100 + f[0] * 1000 + e.length * 10000 + q[0] * 100000;
    }
    function narrow(uint256 x) internal pure returns (uint256 r) {
        uint8[] memory small = new uint8[](2);
        small[0] = uint8(x);
        small[1] = uint8(x >> 8);
        if (x % 5 == 4) {
            small[1] += uint8(x % 64);
        }
        bool[] memory flags = new bool[](3);
        flags[x % 3] = true;
        r = uint256(small[0]) + uint256(small[1]) * 256 + (flags[1] ? 1 << 20 : 0) + (flags[2] ? 1 << 21 : 0);
        if (x % 13 == 12) {
            small[small.length] += 1;
        }
    }
    function rows(uint256 x) internal pure returns (uint256 r) {
        uint256[][] memory m = new uint256[][](3);
        m[1] = new uint256[](2);
        m[0] = m[1];
        m[0][1] = x % 1000;
        r = m[1][1] + m[2].length * 7;
        delete m[1];
        r += m[1].length * 11 + m[0][1] * 3;
        delete m;
        r += m.length * 13;
    }
    function change(uint256 x) external returns (uint256) {
        uint256 n = x % 5;
        uint256[] memory a = new uint256[](n);
        for (uint256 i = 0; i < n; i++) {
            a[i] = (x >> (8 * i)) & 0xffff;
        }
        uint256[] memory b = scaled(a, x % 3);
        bumpAll(a);
        uint256[] memory c = add(a, b);
        (uint256[] memory head, uint256 total) = split(c);
        (uint256[] memory win, uint256 weight) = window(c, x % 4);
        value = win.length * 31 + weight;
        for (uint256 i = 0; i < win.length; i++) {
            value += win[i] * (i + 11);
        }
        uint256[] memory d;
        if (x % 2 == 1) {
            d = c;
        }
        value += total + head.length * 1000 + d.length * 100000 + b.length * 7;
        for (uint256 i = 0; i < head.length; i++) {
            value += head[i] * (i + 3);
        }
        if (x % 7 == 6) {
            value += c[n];
        }
        uint256[][] memory v = new uint256[][](3);
        v[0] = a;
        v[1] = add(a, b);
        if (n > 0) {
            v[1][0] = v[1][0] + 5;
        }
        value += vecSum(v) * 13 + v.length + v[2].length;
        if (x % 11 == 10) {
            v[2][0] = 1;
        }
        value += owners(x) + narrow(x) * 7 + rows(x) * 11;
        last = n == 0 ? 0 : b[0];
        return value;
    }
    function fail() external {
        uint256[] memory probe = new uint256[](value % 3);
        value = probe[value % 3];
    }
    function read() external view returns (uint256, uint256) {
        return (value, last);
    }
}
