// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    struct Balance {
        address asset;
        uint256 amount;
        uint64 total;
        bool active;
    }
    struct UserAssetBalance {
        address asset;
        uint256 userBalance;
        uint256 totalSupply;
    }
    uint256 private value;
    uint256 private last;
    Balance private stored;
    // #2721 issue case: an `S[] memory` helper result passed straight to an `S[]` helper.
    function _getBalances(address asset) internal pure returns (UserAssetBalance[] memory list) {
        list = new UserAssetBalance[](1);
        list[0] = UserAssetBalance({asset: asset, userBalance: 1, totalSupply: 10});
    }
    function _sumBalances(UserAssetBalance[] memory list) internal pure returns (uint256) {
        return list.length;
    }
    // Member-by-member fill of zeroed elements, as Aave's `_getUserAssetBalances`.
    function fill(uint256 x, uint256 n) internal pure returns (UserAssetBalance[] memory list) {
        list = new UserAssetBalance[](n);
        for (uint256 i = 0; i < n; i++) {
            list[i].asset = address(uint160(x + i));
            list[i].userBalance = x % (i + 3);
        }
    }
    function supplyOf(UserAssetBalance memory b) internal pure returns (uint256) {
        return b.userBalance * 3 + b.totalSupply + uint256(uint160(b.asset)) % 5;
    }
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
        uint256 k = 1;
        zeros[k++].total = uint64(k);
        uint64 dirty = 0;
        assembly { dirty := add(shl(64, 1), 3) }
        zeros[0].total = dirty;
        value = zeros[1].total + uint256(zeros[0].total);
        uint8 d = 0;
        assembly { d := 257 }
        Balance[] memory single = new Balance[](d);
        single[0].amount = d;
        zeros[d].amount = single[0].amount;
        value += single.length + single[0].amount + zeros[1].amount;
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
        value += sum(list) * 1000 + sum(zeros) + list.length * 7 + sum(build(x >> 16, 2)) * 100000;
        UserAssetBalance[] memory users = fill(x >> 8, n);
        uint256 supplied = _sumBalances(_getBalances(address(uint160(x)))) * 11;
        for (uint256 i = 0; i < users.length; i++) {
            supplied += supplyOf(users[i]) * (i + 1);
        }
        value += supplied * 10000000;
        // A storage struct is copied into a fresh element; a reassigned array local rebinds.
        stored.amount = x % 13;
        Balance[] memory picked = new Balance[](2);
        if (x % 3 == 1) {
            picked = zeros;
        }
        picked[1] = stored;
        stored.amount = 5;
        value += picked[1].amount * 3 + zeros[1].amount + picked.length;
        if (x % 11 == 10) {
            value += list[n].amount;
        }
        last = n == 0 ? 0 : uint256(uint160(list[0].asset)) + list[0].total;
        return value;
    }
    // A root `S[] memory` parameter shared with helpers and element views.
    function rootShared(Balance[] memory list) external pure returns (uint256) {
        bump(list, 5);
        Balance[] memory view_ = same(list);
        if (list.length > 0) {
            touch(list[0], 4);
            view_[list.length - 1].active = true;
        }
        return sum(list) * 7 + sum(view_) + list.length;
    }
    function fail() external {
        Balance[] memory probe = new Balance[](value % 3);
        value = probe[value % 3].amount;
    }
    function read() external view returns (uint256, uint256) {
        return (value, last);
    }
}
