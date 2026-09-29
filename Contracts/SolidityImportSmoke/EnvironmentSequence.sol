// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// The three names reuse the sequence instrument ABI; fail() observes context.
contract SequenceFixture {
    function change(uint256 value) external view returns (address, address, uint256, uint256, uint256) {
        return (msg.sender, address(this), block.timestamp, block.number, block.chainid);
    }
    function fail() external view returns (uint256) { return block.number; }
    function read() external view returns (address) { return msg.sender; }
}
