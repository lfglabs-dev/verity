pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 total;
    uint8 small;
    uint64 mid;
    mapping(address => uint256) credit;

    function change(uint256 value) external returns (uint256, uint256) {
        uint256 wrapped;
        uint8 t;
        unchecked {
            t = uint8(value % 256) + 250;
            total += value;
            small += uint8(value % 256) + 250;
            mid -= uint64(value % 5) + 1;
            wrapped = value * 3 - 10;
            credit[msg.sender]--;
        }
        uint256 checkedSum = total % 1000 + 1;
        return (wrapped + t, bump(value) + checkedSum);
    }

    function bump(uint256 x) internal pure returns (uint256) {
        unchecked {
            return x - 10 + 3;
        }
    }

    function dec(uint256 x) internal pure returns (uint256) {
        return x - 8;
    }

    function tail(uint256 x) internal pure returns (uint256) {
        unchecked {
            require(x - 3 < 5, "tail");
        }
        return x - 10;
    }

    function fail() external returns (uint256) {
        uint256 r;
        unchecked {
            r = dec(total);
        }
        total = r;
        return r;
    }

    function read() external view returns (uint256, uint256, uint256) {
        return (total + small, mid, credit[msg.sender] % 1000 + tail(total % 16));
    }
}
