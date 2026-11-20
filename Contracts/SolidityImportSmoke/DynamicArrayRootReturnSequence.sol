// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Root return tuples with dynamic `T[] memory` components (#2707): named and
// unnamed, alone or beside scalars, assigned, early-returned and fallen through,
// including a `T[] storage` value returned as `T[] memory` (#2723), which solc
// copies to memory before encoding.
interface IWordProbe { function probe() external; }

library LocalGuard {
    function validate(address, address, uint256 n) internal pure {
        require(n != 3, "library body");
    }
}

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

    // Forward both named helper results without calling it again for the tail.
    function forwardBytes(uint256 x) external returns (bool, bytes memory) {
        return produce(x);
    }

    function produce(uint256 x) private returns (bool flag, bytes memory payload) {
        total ^= x;
        LocalGuard.validate(address(0), address(0), x);
        checkLocal(address(uint160(x == 2 ? 1 : 0)), abi.encodeWithSelector(IWordProbe.probe.selector));
        if (x != 0) {
            flag = true;
            bytes memory packed = abi.encodePacked(uint8(x), total);
            bytes memory mid = passBytes(address(0), packed);
            payload = abi.encodePacked(mid);
            // `first` keeps the old buffer while `payload` is rebound to a new one.
            bytes memory first = payload;
            payload = abi.encodePacked(first, uint8(x >> 8));
        }
    }

    // #2803: a root with named `(bool ok, bytes memory data)` results returns a
    // helper whose results have the same names. Each name is bound per declaration.
    function run(uint256 v) external returns (bool ok, bytes memory data) {
        return _run(v);
    }

    // Root results assigned before the forward are replaced by the helper's.
    function runShadow(uint256 v) external returns (bool ok, bytes memory data) {
        ok = true;
        data = abi.encodePacked(uint16(0xdead));
        return _run(v);
    }

    function _run(uint256 v) private returns (bool ok, bytes memory data) {
        total += v;
        require(v != 3, "run");
        if (v != 0) {
            ok = true;
            data = abi.encodePacked(v);
        }
    }

    function checkLocal(address target, bytes memory) private pure {
        require(target == address(0), "tuple");
    }

    function passBytes(address, bytes memory input) private pure returns (bytes memory) {
        return input;
    }

    function firstMembers() external view returns (address[] memory head) {
        uint256 n = members.length < 2 ? members.length : 2;
        head = new address[](n);
        for (uint256 i = 0; i < n; ++i) {
            head[i] = members[i];
        }
    }
}
