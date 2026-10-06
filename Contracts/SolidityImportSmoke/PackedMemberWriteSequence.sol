// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    struct Box { uint8 low; uint128 middle; uint16 high; uint256 whole; }
    mapping(uint256 => Box) private entries;
    mapping(uint256 => mapping(uint256 => Box)) private pairs;
    uint256 private value;
    event Changed(uint256 value);
    function change(uint256 x) external returns (uint256) {
        entries[1].low = uint8(x);
        entries[1].middle = uint128(x);
        entries[1].high = 65535;
        entries[1].whole = x;
        entries[2].low = 17;
        uint256 key = 1;
        Box storage selected = entries[key];
        key = 2;
        selected.low = 23;
        delete selected.middle;
        require(entries[1].low == 23 && entries[2].low == 17, "alias key");
        require(entries[1].high == 65535 && entries[1].whole == x, "packed siblings");
        require(entries[1].middle == 0, "member delete");
        uint256 left = 3;
        uint256 right = 4;
        pairs[left][right].low = uint8(x);
        pairs[left][right].middle = uint128(x);
        Box storage pair = pairs[left][right];
        left = 5;
        right = 6;
        pair.low = 29;
        delete pair.middle;
        require(pairs[3][4].low == 29 && pairs[5][6].low == 0, "two keys");
        require(pairs[3][4].middle == 0, "pair delete");
        uint256 outer = 3;
        mapping(uint256 => Box) storage row = pairs[outer];
        outer = 8;
        row[4].high = 111;
        require(pairs[3][4].high == 111 && pairs[8][4].high == 0, "outer alias");
        value = entries[1].low + uint256(pairs[3][4].low);
        emit Changed(value);
        return value;
    }
    function fail() external {
        entries[1].low = 255;
        pairs[3][4].high = 65535;
        require(false, "rollback");
    }
    function read() external view returns (uint256) { return value; }
}
