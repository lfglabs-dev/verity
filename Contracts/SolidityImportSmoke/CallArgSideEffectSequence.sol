// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

struct Cell { uint256 word; }
library CellOps {
    function store(Cell storage cell, uint256 next) internal { cell.word = next; }
}

contract SequenceFixture {
    using CellOps for Cell;
    mapping(uint256 => Cell) private cells;
    uint256 private counter;

    function locate(uint256 key) internal returns (Cell storage) { return cells[key]; }
    function pack(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
        return a * 100 + b * 10 + c;
    }
    function change(uint256 x) external returns (uint256) {
        uint256 y = x % 7;
        uint256 beforeWrite = pack(y, y++, y = 9);
        uint256 afterWrite = pack(counter++, y, counter);
        CellOps.store(locate(0), beforeWrite);
        locate(1).store(afterWrite);
        return cells[0].word + cells[1].word;
    }
    function read() external view returns (uint256) { return cells[0].word + cells[1].word; }
    function fail() external returns (uint256) {
        counter = type(uint256).max;
        return pack(1, 2, counter++);
    }
}
