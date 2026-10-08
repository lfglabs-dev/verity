// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface ICallTarget {
    function ping() external returns (bool);
    function notify(uint256 amount) external returns (uint256);
    function settle(address account, uint256 amount, int256 delta, bytes32 tag) external returns (bool);
}

contract SequenceFixture {
    error CallBatchBlocked(uint256 input, bytes32 digest, uint256 totalLen);
    event CallBatchObserved(uint256 indexed totalScore, bytes32 digest, uint256 lengthMetric);

    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private lastLengthMetric;

    function _packEnvelope(bytes memory payload, bytes32 salt) internal pure returns (bytes memory) {
        return bytes.concat(payload, salt, "env");
    }

    function _buildCallBatch(
        address recipient,
        uint256 amount,
        int256 delta,
        bytes32 tag
    ) internal pure returns (bytes memory) {
        bytes memory pingData = abi.encodeCall(ICallTarget.ping, ());
        bytes memory settleData = abi.encodeCall(ICallTarget.settle, (recipient, amount, delta, tag));
        return bytes.concat(pingData, settleData);
    }

    function _measureBuffer(bytes memory buf, uint256 weight) internal pure returns (uint256) {
        return (buf.length * weight) + (uint256(keccak256(buf)) & 0xffffffff);
    }

    function _joinStrings(string memory a, string memory b) internal pure returns (string memory) {
        return string.concat(a, ":", b);
    }

    function change(uint256 input) external returns (uint256) {
        address recipient = address(uint160((input & 0xffffffff) + 0x1000));
        int256 delta = int256(input & 0xffff) - 50;
        bytes32 tagWord = bytes32((input & 0xffffffff) + 7);

        bytes memory batch = _buildCallBatch(recipient, input, delta, tagWord);
        bytes memory sigData = abi.encodeWithSignature(
            "customOp(address,uint256,int256)",
            recipient,
            input,
            int256(-5)
        );
        string memory fullLabel = string.concat(_joinStrings("batch", "v1"), "#ok");

        uint256 inlineCallLen = abi.encodeCall(ICallTarget.notify, (input)).length;
        uint256 totalLen = batch.length + sigData.length + inlineCallLen + bytes(fullLabel).length;
        uint256 bufMetric = _measureBuffer(batch, 2) + _measureBuffer("literal-seed", 5);

        bytes32 digest = keccak256(bytes.concat(batch, sigData, bytes(fullLabel)));

        if (input == 21) {
            revert CallBatchBlocked(input, digest, totalLen);
        }

        uint256 lengthMetric = totalLen + (bufMetric & 0xffffffff);
        totalScore += (uint256(digest) & 0xffffffff) + lengthMetric;
        lastDigest = digest;
        lastLengthMetric = lengthMetric;
        emit CallBatchObserved(totalScore, lastDigest, lastLengthMetric);
        require(input != 20, "bytes memory call batch rollback");
        return totalScore;
    }

    function inspectBytesMemory(
        bytes memory memPayload,
        bytes calldata cdPayload,
        string memory label,
        uint256 tag
    ) external returns (uint256) {
        bytes memory wrappedMem = _packEnvelope(memPayload, bytes32(tag));
        bytes memory copiedCd = cdPayload;
        uint256 memMetric = _measureBuffer(memPayload, 2) + _measureBuffer(wrappedMem, 1);
        uint256 cdMetric = _measureBuffer(cdPayload, 3) + copiedCd.length + cdPayload.length;
        string memory joined = string.concat(label, "!");

        uint256 lenSum = memPayload.length + cdPayload.length;
        bytes memory callData = abi.encodeCall(
            ICallTarget.settle,
            (msg.sender, tag, -3, bytes32(lenSum))
        );
        bytes memory combined = bytes.concat(wrappedMem, copiedCd, callData, bytes(joined));
        bytes32 digest = keccak256(combined);

        uint256 metric = memMetric + cdMetric + combined.length + bytes(joined).length + (tag & 0xffff);
        totalScore += (uint256(digest) & 0xffffffff) + metric;
        lastDigest = digest;
        lastLengthMetric = metric;
        emit CallBatchObserved(totalScore, lastDigest, lastLengthMetric);
        return totalScore;
    }

    function fail() external {
        totalScore += 999;
        bytes memory errBuf = _packEnvelope(abi.encodeCall(ICallTarget.ping, ()), bytes32(uint256(999)));
        bytes32 d = keccak256(errBuf);
        uint256 errLen = errBuf.length;
        revert CallBatchBlocked(999, d, errLen);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        return (totalScore, lastDigest, lastLengthMetric);
    }
}
