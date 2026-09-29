pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 counter;
    uint256 last;
    mapping(address => uint256) credit;

    function tier(uint256 top) internal pure returns (uint256) {
        if (top >= 192) return 3;
        if (top >= 64) {
            return 2;
        } else if (top == 0) {
            return 0;
        }
        return 1;
    }

    function checked(uint256 low) internal pure returns (uint256) {
        if (low / 2 * 2 != low) {
            require(low > 1, "small odd");
        } else {
            require(low > 7 || low == 0, "small even");
        }
        uint256 half = low / 2;
        if (half > 50) {
            uint256 capped = half - 50;
            return capped;
        }
        return half;
    }

    function change(uint256 value) external returns (uint256) {
        if (value == 0) {
            counter = 0;
            return 0;
        }
        uint256 top = value / 0x100000000000000000000000000000000000000000000000000000000000000;
        if (top >= 128) {
            credit[msg.sender] = credit[msg.sender] + top;
        } else {
            credit[msg.sender] = top;
            counter = counter + 1;
        }
        last = tier(top);
        if (credit[msg.sender] > 600) return credit[msg.sender] - 600;
        return checked(value - value / 256 * 256) + last;
    }

    function fail() external returns (uint256) {
        if (counter > last) {
            if (counter - last > 3) {
                last = counter;
                return counter - 3;
            } else {
                require(counter != 2, "unlucky");
            }
        } else if (counter == last) {
            require(false, "equal");
        }
        counter = counter + 1;
        return counter + last;
    }

    function read() external view returns (uint256, uint256, uint256) {
        if (counter > 3) return (counter, last, credit[msg.sender]);
        return (last, counter, 0);
    }
}
