pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private totalSeen;
    uint256 private lastLength;
    mapping(uint256 => uint256) private lengthByTag;
    bool private emptyFlag;

    function getRewardTokens() external view returns (address[] memory) {}

    function redeemRewards(bytes calldata) external returns (uint256[] memory) {}

    function inspectBytes(bytes calldata payload, uint256 tag) external returns (uint256 out) {
        uint256 len = payload.length;
        lastLength = len;
        emptyFlag = (payload.length == 0);
        lengthByTag[tag % 4] = len + tag;
        totalSeen += len + 1;
        out = totalSeen + lengthByTag[tag % 4] + (emptyFlag ? 100 : 0);
    }

    function change(uint256 value) external returns (uint256 out) {
        uint256 tag = value % 4;
        lastLength = value % 17;
        emptyFlag = (lastLength == 0);
        lengthByTag[tag] += lastLength + 1;
        totalSeen += lengthByTag[tag];
        out = totalSeen + lastLength + (emptyFlag ? 10 : 0);
    }

    function fail() external returns (uint256) {
        totalSeen += 99;
        require(lastLength > 1000, "bytes length guard");
        return totalSeen;
    }

    function read() external returns (uint256 out) {
        out = totalSeen + lastLength + lengthByTag[0] + lengthByTag[1] + (emptyFlag ? 1 : 0);
        delete lastLength;
        emptyFlag = false;
    }
}
