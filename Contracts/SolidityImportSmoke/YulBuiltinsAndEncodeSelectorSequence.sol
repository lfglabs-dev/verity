// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface ITokenLike {
    function transfer(address to, uint256 amount) external returns (bool);
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
    function approve(address spender, uint256 amount) external returns (bool);
}

contract SequenceFixture {
    error SelectorBlocked(uint256 input, bytes32 digest);
    event SelectorObserved(uint256 indexed totalScore, bytes32 selectorDigest, uint256 yulMetrics);

    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private lastYulMetrics;

    function _yulContextMix() internal view returns (uint256 result) {
        assembly ("memory-safe") {
            result := xor(add(add(caller(), address()), add(timestamp(), number())), chainid())
        }
    }

    function _yulSdiv(int256 a, int256 b) internal pure returns (int256 result) {
        assembly ("memory-safe") {
            result := sdiv(a, b)
        }
    }

    function _yulSmod(int256 a, int256 b) internal pure returns (int256 result) {
        assembly ("memory-safe") {
            result := smod(a, b)
        }
    }

    function _yulExp(uint256 base, uint256 exponent) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            result := exp(base, exponent)
        }
    }

    function _yulByte(uint256 idx, uint256 word) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            result := byte(idx, word)
        }
    }

    function _yulSignExtend(uint256 byteIdx, uint256 word) internal pure returns (int256 result) {
        assembly ("memory-safe") {
            result := signextend(byteIdx, word)
        }
    }

    function _yulSignedCmp(int256 a, int256 b) internal pure returns (uint256 result) {
        assembly ("memory-safe") {
            result := add(shl(1, slt(a, b)), sgt(a, b))
        }
    }

    function change(uint256 input) external returns (uint256) {
        ITokenLike token = ITokenLike(address(uint160((input % 1000) + 1)));
        address recipient = address(uint160((input % 500) + 10));
        uint256 amount = (input % 100000) + 7;

        bytes memory transferCall = abi.encodeWithSelector(
            ITokenLike.transfer.selector,
            recipient,
            amount
        );
        bytes memory aliasCall = transferCall;
        bytes32 d1 = keccak256(aliasCall);
        bytes32 d2 = keccak256(
            abi.encodeWithSelector(
                token.approve.selector,
                recipient,
                amount
            )
        );
        bytes32 d3 = keccak256(abi.encodeWithSelector(this.read.selector));
        bytes32 d4 = keccak256(
            abi.encodePacked(
                ITokenLike.transfer.selector,
                ITokenLike(recipient).transferFrom.selector,
                this.read.selector
            )
        );
        bytes32 digest = keccak256(abi.encode(d1, d2, d3, d4));

        if (input == 21) {
            revert SelectorBlocked(input, digest);
        }

        int256 signedA = (input % 2 == 0)
            ? -int256((input % 250) + 13)
            : int256((input % 250) + 13);
        int256 signedB = (input % 5 == 0)
            ? int256(0)
            : ((input % 3 == 0) ? -int256((input % 17) + 3) : int256((input % 17) + 3));

        int256 q = _yulSdiv(signedA, signedB);
        int256 r = _yulSmod(signedA, signedB);
        uint256 cmpBits = _yulSignedCmp(signedA, signedB);
        uint256 powVal = _yulExp((input % 7) + 2, input % 9);
        uint256 pickedByte = _yulByte(input % 36, uint256(digest));
        int256 ext0 = _yulSignExtend(0, 0x80 + (input % 127));
        int256 extWide = _yulSignExtend(input % 34, uint256(digest));
        uint256 ctxMix = _yulContextMix();

        uint256 yulMetric = (uint256(q) & 0xffff)
            + ((uint256(r) & 0xffff) << 16)
            + (cmpBits << 32)
            + ((powVal & 0xffffffff) << 40)
            + (pickedByte << 72)
            + ((uint256(ext0) & 0xffff) << 80)
            + ((uint256(extWide) & 0xffff) << 96)
            + (ctxMix & 0xffffffff);

        totalScore += (uint256(digest) & 0xffffffff) + (yulMetric & 0xffffffff);
        lastDigest = digest;
        lastYulMetrics = yulMetric;
        emit SelectorObserved(totalScore, lastDigest, lastYulMetrics);
        require(input != 20, "selector yul rollback");
        return totalScore;
    }

    function fail() external {
        totalScore += 999;
        bytes32 d = keccak256(abi.encodeWithSelector(this.fail.selector));
        revert SelectorBlocked(999, d);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        return (totalScore, lastDigest, lastYulMetrics);
    }
}
