// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Event arguments that read a member of a mapping nested in a mapped storage struct (the
// slot derivation hashes through scratch memory 0x00/0x20 inside the argument prelude), and
// a single checked-arithmetic event argument, which panics before the log on underflow.
contract SequenceFixture {
    struct Entry {
        uint128 index;
        uint88 rate;
    }
    struct Group {
        mapping(address => Entry) entries;
        uint256 total;
    }

    mapping(address => Group) internal groups;
    uint256 private saved;

    event Updated(address indexed owner, address indexed key, uint256 rate);
    event Pair(uint256 first, uint256 second, uint128 index);
    event Accrued(uint256 delta, address indexed owner, uint256 rate);

    function change(uint256 next) external returns (uint256) {
        saved = next;
        address owner = address(uint160(next));
        address key = address(uint160(next >> 96));
        groups[owner].entries[key].rate = uint88(next);
        groups[owner].entries[key].index = uint128(next >> 88);
        emit Updated(owner, key, groups[owner].entries[key].rate);
        emit Pair(groups[owner].entries[key].rate, groups[key].entries[owner].rate,
            groups[owner].entries[key].index);
        emit Accrued(next - 3, owner, groups[owner].entries[key].rate);
        return saved;
    }

    function fail() external {
        saved = 99;
        emit Updated(address(1), address(2), groups[address(1)].entries[address(2)].rate);
        revert();
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
