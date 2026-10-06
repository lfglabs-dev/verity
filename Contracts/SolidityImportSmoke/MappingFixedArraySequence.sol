// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    mapping(address => uint16[7]) internal narrow;
    mapping(address => uint24[12]) internal crossing;
    mapping(address => mapping(uint256 => uint256[3])) internal words;
    event Changed(uint256 value);

    function change(uint256 x) external returns (uint256, uint256, uint256, uint256, uint256) {
        uint256 index = x % 9;
        narrow[msg.sender][0] = 19;
        narrow[msg.sender][6] = 37;
        narrow[msg.sender][index] = uint16(x);
        uint16[7] memory beforeWrite = narrow[msg.sender];
        narrow[msg.sender][index] = 42;
        crossing[msg.sender][9] = 0xabcdef;
        crossing[msg.sender][10] = 0x123456;
        crossing[msg.sender][11] = 0x654321;
        delete crossing[msg.sender][10];
        words[msg.sender][5][2] = 99;
        uint256 observed = crossing[msg.sender][11];
        emit Changed(observed);
        return (beforeWrite[index], narrow[msg.sender][index], crossing[msg.sender][9], crossing[msg.sender][11], words[msg.sender][5][2]);
    }
    function fail() external {
        crossing[msg.sender][9] = 123;
        emit Changed(123);
        require(false, "array rollback");
    }
    function read() external view returns (uint256, uint256, uint256, uint256, uint256, uint256) {
        return (narrow[msg.sender][0], narrow[msg.sender][6], crossing[msg.sender][9], crossing[msg.sender][10], crossing[msg.sender][11], words[msg.sender][5][2]);
    }
}
