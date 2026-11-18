// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Non-indexed `string` event parameters: each is ABI-encoded into the log data as an
// offset word, a length word and the right-padded bytes, next to value-type data and
// beside indexed topics.
contract SequenceFixture {
    event Labeled(uint64 indexed id, string label);
    event Noted(string note, uint256 indexed value, string tail);
    event Pair(string first, uint256 amount, string second);

    uint256 private saved;

    function change(uint256 next) external returns (uint256) {
        saved = next;
        emit Labeled(uint64(next), "a literal label longer than one thirty-two byte word");
        string memory text = string(abi.encodePacked("v", next));
        emit Noted(text, next, "");
        uint256 amount = next % 7;
        emit Pair(string.concat("<", text, ">"), amount, text);
        return saved;
    }

    function label(uint64 id, string calldata text) external returns (uint256) {
        saved = id;
        emit Labeled(id, text);
        emit Noted(text, saved, string.concat(text, text));
        return saved;
    }

    function fail() external {
        saved = 99;
        emit Labeled(7, "dropped");
        revert();
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
