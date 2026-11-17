// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `revert(string)` and `require(bool, string)` with computed `string memory`
// messages: exact `Error(string)` bytes for empty, short, word-sized and long
// messages, and a message helper that reverts even when the condition holds.
contract SequenceFixture {
    bytes16 private constant HEX_SYMBOLS = "0123456789abcdef";
    uint256 private saved;

    function toHexString(uint256 value, uint256 length) internal pure returns (string memory) {
        bytes memory buffer = new bytes(2 * length + 2);
        buffer[0] = "0";
        buffer[1] = "x";
        for (uint256 i = 2 * length + 1; i > 1; --i) {
            buffer[i] = HEX_SYMBOLS[value & 0xf];
            value >>= 4;
        }
        require(value == 0, "hex length insufficient");
        return string(buffer);
    }

    function change(uint256 next) external returns (uint256) {
        saved = next;
        if (next % 5 == 1) {
            revert(string(abi.encodePacked("one mod five: ", bytes32(next))));
        }
        require(next % 5 != 2, string.concat("two mod five ", "rejected"));
        string memory reason = next % 5 == 3 ? "" : "four mod five: a reason longer than one word";
        require(next % 5 == 0 || next % 5 == 1, reason);
        require(next < 1000 || next > 65535, string(abi.encodePacked("bounded ", toHexString(next, 2))));
        return saved;
    }

    function fail() external {
        saved = 99;
        revert(string(abi.encodePacked("fail ", saved)));
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
