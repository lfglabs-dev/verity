// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `<param>.slot` of a storage struct helper parameter in inline assembly, for
// top-level, single-key and two-key mapping struct paths, read with `sload`,
// written with `sstore`, returned as a word, and used as a transient slot
// (`tload` / `tstore` of `not(self.slot)`) through a library receiver.

struct TransientWord {
    uint256 _placeholder;
}

library TransientWordAccess {
    function tget(TransientWord storage self) internal view returns (uint256 value) {
        assembly ("memory-safe") {
            value := tload(not(self.slot))
        }
    }

    function tset(TransientWord storage self, uint256 value) internal {
        assembly ("memory-safe") {
            tstore(not(self.slot), value)
        }
    }
}

contract SequenceFixture {
    using TransientWordAccess for TransientWord;

    struct Cell {
        uint128 lo;
        uint128 hi;
        uint256 word;
    }

    uint256 private total;
    Cell private top;
    mapping(uint256 => Cell) private cells;
    mapping(address => mapping(uint256 => Cell)) private grid;
    TransientWord private lock;
    mapping(uint256 => TransientWord) private locks;

    function _slotOf(Cell storage self) internal pure returns (uint256 s) {
        assembly {
            s := self.slot
        }
    }

    function _rawWord(Cell storage self, uint256 offset) internal view returns (uint256 v) {
        assembly {
            v := sload(add(self.slot, offset))
        }
    }

    function _rawStore(Cell storage self, uint256 v) internal {
        assembly {
            sstore(add(self.slot, 1), v)
        }
    }

    function _stateTopSlot() internal pure returns (uint256 s) {
        assembly {
            s := top.slot
        }
    }

    // The parameter shadows the state variable `top`: the callee's `top.slot`
    // is the state variable's slot, not the caller's parameter slot.
    function _shadowedSlots(Cell storage top) internal pure returns (uint256) {
        uint256 own;
        assembly {
            own := top.slot
        }
        return own ^ (_stateTopSlot() << 1);
    }

    function _fill(Cell storage self, uint256 x) internal returns (uint256) {
        self.lo = uint128(x);
        self.hi = uint128(x >> 130);
        _rawStore(self, x ^ 0xabc);
        return _rawWord(self, 0) ^ self.word;
    }

    function change(uint256 x) external returns (uint256) {
        uint256 key = x % 3;
        uint256 acc = _fill(top, x);
        acc ^= _fill(cells[key], x ^ 1);
        acc ^= _fill(grid[msg.sender][key], x ^ 2);
        acc ^= _slotOf(top) ^ _slotOf(cells[key]) ^ _slotOf(grid[msg.sender][key]);
        acc ^= _shadowedSlots(cells[key]);
        uint256 small = x & 0xffffffff;
        lock.tset(small);
        locks[key].tset(small + 5);
        small += lock.tget() + locks[key].tget() + locks[(key + 1) % 3].tget();
        total = (total ^ acc) + (small & 0xffff);
        require(x != 20, "storage struct slot rollback");
        return total;
    }

    function fail() external {
        lock.tset(1);
        top.word = 7;
        revert("storage struct slot failure");
    }

    function read() external view returns (uint256, uint256, uint256, uint256, uint256) {
        return (total, _rawWord(top, 0), _rawWord(cells[1], 1), top.word ^ cells[2].word, _slotOf(grid[msg.sender][2]));
    }
}
