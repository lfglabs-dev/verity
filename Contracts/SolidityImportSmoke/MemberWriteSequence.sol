pragma solidity 0.8.34;

contract SequenceFixture {
    struct State {
        uint8 spacing;
        uint16 fee0;
        uint16 fee1;
        uint32 continuous;
        uint128 units;
        uint128 credit;
        uint256 wide;
    }

    uint256 total;
    mapping(bytes32 => State) states;
    mapping(bytes32 => mapping(address => State)) positions;

    function change(uint256 value) external returns (uint256, uint256) {
        bytes32 id = bytes32(value % 4);
        State storage s = states[id];
        s.spacing = uint8(value % 200);
        s.fee0 = uint16(value % 1000);
        s.fee1 += 3;
        s.fee1++;
        states[id].continuous = uint32(value % 4294967296);
        states[id].units += uint128(value % 1000000);
        State storage p = positions[id][msg.sender];
        p.credit = uint128(value % 1000) + p.credit;
        positions[id][msg.sender].wide += value % 1000 + 1;
        total += value % 1000 + 1;
        return (s.spacing + s.fee0, p.credit);
    }

    function fail() external returns (uint256) {
        // solc evaluates the divisor before the underflowing key.
        states[bytes32(total - 9)].wide -= 100 / (total % 4);
        State storage s = states[bytes32(total % 4)];
        s.wide -= total;
        s.fee0 /= uint16(total % 3);
        delete positions[bytes32(total % 4)][msg.sender].credit;
        total -= 1;
        return s.wide;
    }

    function read() external view returns (uint256, uint256, uint256) {
        State storage s = states[bytes32(total % 4)];
        return (s.units + s.continuous, positions[bytes32(total % 4)][msg.sender].credit, s.fee1);
    }
}
