// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `for (...; i < values.length; ...)` over a dynamic storage array. solc re-reads the
// length before every test; the body writes array elements, a mapping and a scalar and
// calls a `view` helper, none of which can change the length, so reading it once is
// exact. Pushes and pops between transactions move the length, including to zero.
contract SequenceFixture {
    uint256[] private values;
    mapping(uint256 => uint256) private seen;
    uint256 private total;

    function _weight(uint256 v) internal view returns (uint256) {
        return seen[v % 7] + 1;
    }

    function _scaled() internal view returns (uint256 acc) {
        for (uint256 i = 0; i < values.length; i++) {
            acc += values[i] * _weight(values[i]);
        }
    }

    function change(uint256 x) external returns (uint256) {
        if (x % 5 == 0 && values.length > 0) {
            values.pop();
        } else {
            values.push(x % 1000);
        }
        uint256 sum;
        for (uint256 i = 0; i < values.length; ++i) {
            sum += values[i];
            values[i] = values[i] + 1;
            seen[values[i] % 7] += 1;
        }
        total += sum + _scaled();
        return total;
    }

    function fail() external {
        values.push(7);
        for (uint256 i = 0; i < values.length; i++) {
            total += values[i];
        }
        revert();
    }

    function read() external view returns (uint256, uint256) {
        return (total, values.length);
    }
}
