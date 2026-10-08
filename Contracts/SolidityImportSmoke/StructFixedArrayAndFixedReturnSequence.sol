// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    struct Position {
        uint128 credit;
        uint64 epoch;
        uint128[3] collateral;
        uint16[3] fees;
    }

    struct Pool {
        uint256 total;
        uint256[2] buckets;
    }

    mapping(bytes32 => mapping(address => Position)) private position;
    mapping(bytes32 => Pool) private pool;
    mapping(bytes32 => uint16[3]) private settlementFeeCbps;

    function change(uint256 input) external returns (uint256[3] memory) {
        bytes32 id = bytes32(uint256(1));
        uint256 seed = input % 10000;
        uint256 writeIdx = (input == 19) ? 3 : (input % 3);
        uint256 readIdx = (input == 21) ? 3 : (input % 3);

        position[id][msg.sender].credit += uint128(seed);
        position[id][msg.sender].collateral[0] = 11;
        position[id][msg.sender].collateral[2] = 33;
        position[id][msg.sender].collateral[writeIdx] = uint128(seed);

        uint128[3] memory snap = position[id][msg.sender].collateral;
        position[id][msg.sender].collateral[0] = 42;

        position[id][msg.sender].fees[0] = 15;
        position[id][msg.sender].fees[1] = 25;
        position[id][msg.sender].fees[2] = 35;
        delete position[id][msg.sender].fees[1];

        pool[id].total += seed;
        pool[id].buckets[0] = seed;
        pool[id].buckets[1] = position[id][msg.sender].collateral[2];

        settlementFeeCbps[id][0] = uint16(position[id][msg.sender].collateral[readIdx]);
        settlementFeeCbps[id][1] = position[id][msg.sender].fees[1];
        settlementFeeCbps[id][2] = position[id][msg.sender].fees[2];

        require(input != 20, "struct fixed array rollback");
        return [
            uint256(snap[readIdx]),
            pool[id].total,
            pool[id].buckets[1]
        ];
    }

    function fail() external {
        bytes32 id = bytes32(uint256(1));
        position[id][msg.sender].collateral[0] = 999;
        settlementFeeCbps[id][0] = 777;
        require(false, "struct fixed array fail");
    }

    function read() external view returns (uint16[3] memory) {
        bytes32 id = bytes32(uint256(1));
        uint16[3] memory fees = settlementFeeCbps[id];
        return fees;
    }
}
