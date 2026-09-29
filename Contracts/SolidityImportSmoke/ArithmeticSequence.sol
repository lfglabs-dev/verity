pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 total;
    uint256 last;
    uint8 ticks;
    mapping(address => uint256) credit;
    mapping(uint256 => mapping(address => uint256)) shares;

    function change(uint256 value) external returns (uint256, uint256) {
        uint256 low = value % 1000;
        total += low + 10;
        credit[msg.sender] += low % 7 + 1;
        shares[low % 3][msg.sender] += low;
        shares[low % 3][msg.sender] *= 3;
        shares[low % 3][msg.sender] -= 4;
        total /= low % 4 + 1;
        total %= 1000;
        if (low % 2 == 1) {
            ticks += 50;
        } else {
            ticks--;
        }
        last = low / 2;
        last++;
        return (total % 97, value % (last + 1));
    }

    function fail() external returns (uint256) {
        // solc evaluates the divisor before the underflowing key.
        shares[total - last - 4][msg.sender] -= 100 / (total % 4);
        ticks -= 1;
        --last;
        total %= last;
        return total;
    }

    function read() external view returns (uint256, uint256, uint8) {
        return (credit[msg.sender] % 1000, shares[1][msg.sender], ticks);
    }
}
