// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Inline-assembly assignments of dirty words to `bool` / `address` locals and a named `bool`
// helper result (via-IR): the cleaned words reach branches, comparisons, conversions, a packed
// storage slot and an event exactly as solc's cleanup leaves them.
contract SequenceFixture {
    uint256 private total;
    bool private flag;
    address private owner;

    event Observed(bool flag, address owner);

    function _successOf(uint256 w) private pure returns (bool success) {
        assembly { success := and(w, 0xff00) }
    }

    function change(uint256 x) external returns (uint256) {
        bool ok;
        address a;
        assembly {
            ok := shr(1, x)
            a := not(x)
        }
        flag = ok;
        owner = a;
        emit Observed(ok, a);
        if (ok) total = total + 1;
        if (ok == _successOf(x)) total = total + 2;
        if (a == address(uint160(~x))) total = total + 4;
        total = total + uint160(a) % 1000;
        return total;
    }

    // The stateful harness's reverting call: its write is rolled back.
    function fail() external {
        total = total + 1;
        revert();
    }

    function read() external view returns (uint256) {
        return total;
    }
}
