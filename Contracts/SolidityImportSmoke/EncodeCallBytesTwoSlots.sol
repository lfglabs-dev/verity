// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `abi.encodeCall` of a target with a `bytes` parameter (#2830): the selector, then the
// arguments ABI-encoded against the declared parameter types. `EncodeCallBytesOneSlot.sol`
// is this contract without one unrelated state variable and one unused function; both must
// import to the same model.

interface IBytesTarget {
    function take(bytes calldata data) external;
    function mixed(uint256 amount, bytes calldata data, address who) external;
    function pair(bytes calldata first, uint256 tag, bytes calldata second) external;
}

contract EncodeCallBytesTwoSlots {
    error Rejected(uint256 code);

    bytes private stored;
    uint256 private unused;

    function sample(uint256 n) internal pure returns (bytes memory) {
        if (n == 0) return "";
        if (n == 1) return "0123456789abcdef0123456789abcde";
        if (n == 2) return "0123456789abcdef0123456789abcdef";
        if (n == 3) return "0123456789abcdef0123456789abcdef0";
        return "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789";
    }

    function failing(uint256 x) internal pure returns (bytes memory) {
        if (x < 3) revert Rejected(2);
        return "ok";
    }

    function literalEmpty() external pure returns (bytes32) {
        return keccak256(abi.encodeCall(IBytesTarget.take, ("")));
    }

    function literalLong() external pure returns (bytes32) {
        return keccak256(abi.encodeCall(IBytesTarget.take, ("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789")));
    }

    function memoryArg(uint256 n) external pure returns (bytes32) {
        bytes memory b = sample(n);
        return keccak256(abi.encodeCall(IBytesTarget.take, (b)));
    }

    function memoryLength(uint256 n) external pure returns (uint256) {
        bytes memory b = sample(n);
        return abi.encodeCall(IBytesTarget.take, (b)).length;
    }

    function helperArg(uint256 n) external pure returns (bytes32) {
        return keccak256(abi.encodeCall(IBytesTarget.take, (sample(n))));
    }

    function calldataArg(bytes calldata b) external pure returns (bytes32) {
        return keccak256(abi.encodeCall(IBytesTarget.take, (b)));
    }

    function storageArg(uint256 n) external returns (bytes32) {
        stored = sample(n);
        return keccak256(abi.encodeCall(IBytesTarget.take, (stored)));
    }

    function staticSiblings(uint256 amount, bytes calldata b, address who) external pure returns (bytes32) {
        return keccak256(abi.encodeCall(IBytesTarget.mixed, (amount, b, who)));
    }

    function dynamicSiblings(bytes calldata a, uint256 tag, uint256 n) external pure returns (bytes32) {
        bytes memory second = sample(n);
        return keccak256(abi.encodeCall(IBytesTarget.pair, (a, tag, second)));
    }

    function helperRevert(uint256 x, uint256 amount) external pure returns (bytes32) {
        return keccak256(abi.encodeCall(IBytesTarget.mixed, (amount, failing(x), address(0))));
    }

    function returned(uint256 n) external pure returns (bytes memory) {
        return abi.encodeCall(IBytesTarget.take, (sample(n)));
    }

    function touchUnused(uint256 x) external {
        unused = x;
    }
}
