// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract TypedAccessFixture {
    function read() external pure returns (uint256) { return 45; }
    function noop() external pure { }
    function fail() external pure { require(false, "typed failure"); }
}
