// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    error ContextBlocked(uint256 input, address originAddr, bytes32 digest);
    error ArrayLengthMismatch(uint256 amountsLen, uint256 recipientsLen);
    event ContextAndArrayObserved(uint256 indexed totalScore, bytes32 digest, uint256 contextMetric);

    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private lastContextMetric;

    function _yulSelfBalance() internal view returns (uint256 result) {
        assembly ("memory-safe") {
            result := selfbalance()
        }
    }

    function _yulOrigin() internal view returns (address result) {
        assembly ("memory-safe") {
            result := origin()
        }
    }

    function _concat(string memory a, string memory b) internal pure returns (string memory) {
        return string(abi.encodePacked(a, b));
    }

    function _labelCalldataMetric(string calldata s) internal pure returns (uint256) {
        return bytes(s).length + (uint256(keccak256(bytes(s))) & 0xffff);
    }

    function _headBonus(uint256[] memory vals, address[] memory addrs) internal pure returns (uint256) {
        if (vals.length == 0 || addrs.length == 0) {
            return 0;
        }
        return (vals[0] & 0xffff) + (uint256(uint160(addrs[0])) & 0xffff);
    }

    function _sumMemory(uint256[] memory vals, address[] memory addrs) internal pure returns (uint256) {
        uint256 acc = _headBonus(vals, addrs);
        for (uint256 i = 0; i < vals.length; i++) {
            acc += (vals[i] & 0xffffffff) + (uint256(uint160(addrs[i])) & 0xffff) + i;
        }
        return acc;
    }

    function _sumCalldata(uint256[] calldata vals, address[] calldata addrs) internal pure returns (uint256) {
        uint256 acc = 0;
        for (uint256 i = 0; i < vals.length; i++) {
            acc += ((vals[i] & 0xffffffff) ^ (uint256(uint160(addrs[i])) & 0xffff)) + (i * 3);
        }
        return acc;
    }

    function _sumNarrowMemory(uint64[] memory caps) internal pure returns (uint256) {
        uint256 acc = 0;
        for (uint256 i = 0; i < caps.length; i++) {
            acc += uint256(caps[i]) + (i * 5);
        }
        return acc;
    }

    function change(uint256 input) external returns (uint256) {
        uint256 balA = address(this).balance;
        uint256 balB = payable(address(this)).balance;
        uint256 balYul = _yulSelfBalance();
        address origSol = tx.origin;
        address origYul = _yulOrigin();

        string memory baseTag = "tag:";
        string memory rightTag = "ok";
        string memory combined = _concat(baseTag, rightTag);
        string memory wrapped = string(abi.encodePacked(combined, ":end"));

        uint256 strMetric = bytes(baseTag).length + bytes(combined).length + bytes(wrapped).length;
        uint256 balSum = balA + balB + balYul;
        bytes32 digest = keccak256(
            abi.encodePacked(
                bytes(combined),
                wrapped,
                origSol,
                origYul,
                balSum,
                input
            )
        );

        if (input == 21) {
            revert ContextBlocked(input, origSol, digest);
        }

        uint256 ctxMetric = balSum
            + (uint256(uint160(origSol)) & 0xffffffff)
            + (uint256(uint160(origYul)) & 0xffffffff)
            + strMetric;

        totalScore += (uint256(digest) & 0xffffffff) + ctxMetric;
        lastDigest = digest;
        lastContextMetric = ctxMetric;
        emit ContextAndArrayObserved(totalScore, lastDigest, lastContextMetric);
        require(input != 20, "context array rollback");
        return totalScore;
    }

    function inspectArraysAndStrings(
        uint256[] calldata amounts,
        address[] calldata recipients,
        string calldata label,
        uint256 tag
    ) external returns (uint256) {
        uint256 amountsLen = amounts.length;
        uint256 recipientsLen = recipients.length;
        require(
            amountsLen == recipientsLen,
            ArrayLengthMismatch(amountsLen, recipientsLen)
        );

        bytes32 rolling = keccak256(bytes(label));
        for (uint256 i = 0; i < amounts.length; i++) {
            address recipient = recipients[i];
            uint256 amount = amounts[i];
            rolling = keccak256(abi.encode(rolling, recipient, amount, i));
        }

        uint256 cdSum = _sumCalldata(amounts, recipients);
        uint256 memSum = _sumMemory(amounts, recipients);
        string memory fullLabel = _concat(label, "!");
        uint256 labelMetric = _labelCalldataMetric(label) + bytes(fullLabel).length;
        bytes32 finalDigest = keccak256(abi.encodePacked(rolling, fullLabel, label, tag));

        uint256 metric = cdSum + memSum + labelMetric + amounts.length + (tag & 0xffff);
        totalScore += (uint256(finalDigest) & 0xffffffff) + metric;
        lastDigest = finalDigest;
        lastContextMetric = metric;
        emit ContextAndArrayObserved(totalScore, lastDigest, lastContextMetric);
        return totalScore;
    }

    function inspectNarrowArray(
        uint64[] calldata caps,
        uint256 scale
    ) external returns (uint256) {
        uint256 direct = 0;
        for (uint256 i = 0; i < caps.length; i++) {
            direct += uint256(caps[i]) * ((scale & 0xff) + 1);
        }
        uint256 memTotal = _sumNarrowMemory(caps);
        uint256 metric = direct + memTotal + caps.length;
        totalScore += metric;
        lastContextMetric = metric;
        emit ContextAndArrayObserved(totalScore, lastDigest, lastContextMetric);
        return totalScore;
    }

    function fail() external {
        totalScore += 999;
        string memory reasonTag = _concat("fail:", "revert");
        bytes32 d = keccak256(bytes(reasonTag));
        address orig = tx.origin;
        revert ContextBlocked(999, orig, d);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        return (totalScore, lastDigest, lastContextMetric);
    }
}
