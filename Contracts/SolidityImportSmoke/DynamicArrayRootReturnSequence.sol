// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Root return tuples with dynamic `T[] memory` components (#2707): named and
// unnamed, alone or beside scalars, assigned, early-returned and fallen through,
// including a `T[] storage` value returned as `T[] memory` (#2723), which solc
// copies to memory before encoding.
contract SequenceFixture {
    address[] private members;
    uint256 private total;

    function change(uint256 x) external returns (address[] memory added, uint256[] memory amounts) {
        uint256 n = x % 4;
        added = new address[](n);
        amounts = new uint256[](n);
        for (uint256 i = 0; i < n; ++i) {
            address member = address(uint160(x >> (8 * i)));
            members.push(member);
            added[i] = member;
            amounts[i] = x / (i + 1);
            total = total ^ amounts[i];
        }
        if (x % 7 == 6) return (members, amounts);
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external view returns (address[] memory) {
        return members;
    }

    function snapshot() external view returns (uint256 count, address[] memory all, uint256 sum) {
        count = members.length;
        return (count, members, total);
    }

    function firstMembers() external view returns (address[] memory head) {
        uint256 n = members.length < 2 ? members.length : 2;
        head = new address[](n);
        for (uint256 i = 0; i < n; ++i) {
            head[i] = members[i];
        }
    }
}
