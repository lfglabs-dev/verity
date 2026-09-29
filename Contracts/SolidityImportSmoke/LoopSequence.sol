pragma solidity 0.8.34;

contract SequenceFixture {
    struct Pos {
        uint128 a;
        uint128 b;
    }

    uint256 total;
    uint256 count;
    mapping(uint256 => uint256) slots;
    mapping(uint256 => mapping(address => uint256)) credit;
    mapping(uint256 => Pos) pos;

    function change(uint256 value) external returns (uint256, uint256) {
        uint256 n = value % 6;
        uint256 acc;
        uint256 last = 1;
        for (uint256 i = 0; i < n; i++) {
            acc += i * 3 + 1;
            slots[i] += value % 100 + i;
            last = last * 2 + i;
            if (i % 2 == 1) {
                credit[i][msg.sender]++;
            } else {
                count += 1;
            }
        }
        for (uint256 j; j < 3; ++j) {
            total += j;
        }
        uint256 key = n;
        Pos storage p = pos[key];
        key += 1;
        p.a += 5;
        pos[key].b += 1;
        uint256 k = n;
        k -= n / 2;
        total += acc;
        return (acc, last + k);
    }

    function fail() external returns (uint256) {
        uint256 acc = total;
        for (uint256 i = 0; i < 4; i += 1) {
            slots[i] -= 1;
            acc -= i;
        }
        total = acc;
        return acc;
    }

    function read() external view returns (uint256, uint256, uint256) {
        uint256 sum;
        for (uint256 i = 0; i < 6; i++) {
            sum += slots[i] + credit[i][msg.sender] + pos[i].a * 1000 + pos[i].b;
        }
        return (sum, total, count);
    }
}
