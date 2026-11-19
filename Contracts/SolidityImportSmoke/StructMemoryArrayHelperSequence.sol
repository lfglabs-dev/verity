// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    struct Balance {
        address asset;
        uint256 amount;
        uint64 total;
        bool active;
    }
    uint256 private value;
    uint256 private last;
    function build(uint256 x, uint256 n) internal pure returns (Balance[] memory list) {
        list = new Balance[](n);
        for (uint256 i = 0; i < n; i++) {
            list[i] = Balance({asset: address(uint160(x + i)), amount: (x >> (8 * i)) & 0xff,
                total: uint64(i + 1), active: i % 2 == 0});
        }
    }
    function zeroed(uint256 n) internal pure returns (Balance[] memory) {
        return new Balance[](n);
    }
    function sum(Balance[] memory list) internal pure returns (uint256 s) {
        for (uint256 i = 0; i < list.length; i++) {
            s += list[i].amount * list[i].total + (list[i].active ? 1 : 0);
        }
    }
    function bump(Balance[] memory list, uint256 k) internal pure {
        for (uint256 i = 0; i < list.length; i++) {
            list[i].amount = list[i].amount + k;
        }
    }
    function same(Balance[] memory list) internal pure returns (Balance[] memory) {
        return list;
    }
    function touch(Balance memory b, uint64 k) internal pure {
        b.total = k;
    }
    function change(uint256 x) external returns (uint256) {
        uint256 n = x % 4;
        Balance[] memory list = build(x, n);
        bump(list, 3);
        Balance[] memory shared = same(list);
        Balance[] memory zeros = zeroed(2);
        zeros[1].amount = x % 7;
        if (n > 0) {
            shared[0].amount = 100;
            touch(list[n - 1], 9);
            Balance memory first = list[0];
            first.total = 50;
            list[n - 1] = zeros[1];
            zeros[1].total = 77;
            if (x % 5 == 4) {
                delete list[0];
                first.active = true;
            }
        }
        value = sum(list) * 1000 + sum(zeros) + list.length * 7 + sum(build(x >> 16, 2)) * 100000;
        if (x % 11 == 10) {
            value += list[n].amount;
        }
        last = n == 0 ? 0 : uint256(uint160(list[0].asset)) + list[0].total;
        return value;
    }
    function fail() external {
        Balance[] memory probe = new Balance[](value % 3);
        value = probe[value % 3].amount;
    }
    function read() external view returns (uint256, uint256) {
        return (value, last);
    }
}
