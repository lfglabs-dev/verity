// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    struct Box { uint8 low; uint128 middle; uint16 high; }
    mapping(uint256 => uint256) private entries;
    mapping(uint256 => Box) private boxes;
    uint256 private value;
    event Changed(uint256 value);
    function update(uint256 x) internal returns (uint256) {
        uint256 scratch = x;
        scratch = scratch + 1;
        value = scratch;
        entries[1] = x;
        Box storage selected = boxes[2];
        selected.low = uint8(x);
        selected.middle = uint128(x);
        selected.high = 65535;
        delete selected.low;
        require(selected.high == 65535 && selected.middle == uint128(x), "helper siblings");
        if (x < 8) {
            value = value + 2;
        } else {
            delete entries[1];
        }
        return value;
    }
    function never() internal returns (bool) { value = 999; return true; }
    function change(uint256 x) external returns (uint256) {
        uint256 result = update(x);
        require(true || never(), "dead effect");
        require(value == result, "dead helper write");
        value = result + 10;
        emit Changed(value);
        return value;
    }
    function fail() external {
        uint256 result = update(3);
        require(result > 100, "rollback");
    }
    function read() external view returns (uint256) { return value; }
}
