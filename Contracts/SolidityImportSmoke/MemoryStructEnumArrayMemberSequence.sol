// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    enum Mode { None, Stable, Variable }
    struct Repay {
        uint256 amount;
        Mode mode;
        bool flag;
    }
    struct Flash {
        address receiver;
        address[] assets;
        uint256[] amounts;
        uint256 tag;
    }
    uint256 private value;
    uint256 private last;
    function makeRepay(uint256 a, uint256 m) internal pure returns (Repay memory) {
        return Repay(a, Mode(m), a % 2 == 1);
    }
    function weight(Repay memory r) internal pure returns (uint256) {
        if (r.mode == Mode.Variable) {
            return r.amount * 3;
        }
        if (r.mode == Mode.Stable) {
            return r.amount * 2 + (r.flag ? 1 : 0);
        }
        return r.amount;
    }
    function total(Flash memory f) internal pure returns (uint256 s) {
        for (uint256 i = 0; i < f.assets.length; i++) {
            s += uint256(uint160(f.assets[i])) % 1000 + f.amounts[i];
        }
        s += f.tag + f.amounts.length * 11;
    }
    function change(uint256 x) external returns (uint256) {
        Repay memory r = Repay({amount: x % 1000, mode: Mode(x % 3), flag: false});
        if (x % 4 == 1) {
            r.mode = x % 8 == 1 ? Mode.Variable : Mode.None;
        }
        Repay memory q = makeRepay(x % 77, (x >> 8) % 3);
        value = weight(r) + weight(q) * 10 + uint256(q.mode) * 100 + uint256(r.mode) * 1000;
        uint256 n = x % 3 + 1;
        address[] memory assets = new address[](n);
        uint256[] memory amounts = new uint256[](n);
        for (uint256 i = 0; i < n; i++) {
            assets[i] = address(uint160(x + i));
            amounts[i] = i * 5;
        }
        Flash memory f = Flash({receiver: msg.sender, assets: assets, amounts: amounts, tag: n});
        assets[0] = address(uint160(x >> 4));
        amounts[n - 1] = 42;
        value += total(f) * 10000 + f.assets.length * 7;
        if (x % 7 == 6) {
            value += uint256(Mode((x >> 3) % 5));
        }
        if (x % 13 == 12) {
            value += f.amounts[n];
        }
        last = f.receiver == msg.sender ? uint256(uint160(f.assets[0])) : 0;
        return value;
    }
    function fail() external {
        Repay memory r = Repay({amount: 1, mode: Mode(value % 2 + 3), flag: true});
        value = r.amount;
    }
    function read() external view returns (uint256, uint256) {
        return (value, last);
    }
}
