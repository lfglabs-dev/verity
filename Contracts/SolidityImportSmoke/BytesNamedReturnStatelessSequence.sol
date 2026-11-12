// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// No state variables: the `stateVars.size > 1` gates of the importer are all
// off, so this runs the stateless lowering of named `bytes` returns, slice
// arguments and bytes-member structs (the shape of #2623).
contract SequenceFixture {
    struct Parts {
        bytes head;
        bytes tail;
    }

    function tag(bytes memory input, uint8 domain) internal pure returns (bytes memory out) {
        out = abi.encodePacked(domain, keccak256(input));
    }

    function echo(bytes calldata data) external pure returns (bytes memory out) {
        out = data;
    }

    function echoCalldata(bytes calldata data, uint256 start) external pure returns (bytes calldata out) {
        out = data[start:];
    }

    function check(bytes calldata ctx, bytes calldata m, bytes calldata sig) external pure returns (bool) {
        require(ctx.length <= 255, "ctx");
        bytes memory mPrime = abi.encodePacked(bytes1(0), bytes1(uint8(ctx.length)), ctx, m);
        bytes memory h = tag(abi.encodePacked(sig[0:32], mPrime), 1);
        return keccak256(h) == keccak256(sig[32:65]);
    }

    function split(bytes calldata data) internal pure returns (Parts memory) {
        return Parts({head: data[0:32], tail: data[32:data.length]});
    }

    function first(bytes calldata data) external pure returns (bytes32) {
        return keccak256(split(data).head);
    }

    function digest(bytes calldata part) internal pure returns (bytes32) {
        return keccak256(part);
    }

    function digestSlice(bytes calldata data) external pure returns (bytes32) {
        return digest(data[0:32]);
    }

    // A conditional calldata argument is memory-backed in the callee; its
    // slice passed to a `bytes memory` parameter is copied, as from calldata.
    function memoryPart(bytes memory part) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(part, uint8(part.length)));
    }

    function conditionalPart(bytes calldata part, uint256 start) internal pure returns (bytes32) {
        return memoryPart(part[start:]) ^ keccak256(part);
    }

    function conditionalSlice(bytes calldata data, bytes calldata other, uint256 pick) external pure returns (bytes32) {
        return conditionalPart(pick % 2 == 0 ? data : other, pick / 2);
    }

    function change(uint256 x) external pure returns (bytes memory out) {
        if (x % 2 == 0) return out;
        out = tag(abi.encodePacked(x), uint8(x));
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external pure returns (uint256) {
        return 0;
    }
}
