// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

struct Acc {
    uint256 amount;
    address who;
}

contract Store {
    Acc public data;
    uint256 public other;

    function set(Acc memory a) external {
        data = a;
    }

    function get() external view returns (Acc memory) {
        return data;
    }

    function setOther(uint256 n) external {
        other = n;
    }

    function make(uint256 amount, address who) external pure returns (Acc memory) {
        return Acc({amount: amount, who: who});
    }

    function makeRev(uint256 amount, address who) external pure returns (Acc memory) {
        return Acc({who: who, amount: amount});
    }
}
