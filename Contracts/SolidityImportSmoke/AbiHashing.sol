// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {Market} from "pinned-midnight/interfaces/IMidnight.sol";

import {IdLib} from "pinned-midnight/libraries/IdLib.sol";

struct HashStatic { uint128 small; address who; bool enabled; bytes32 tag; }
struct HashArrays { uint128 tag; uint128[] left; uint256[] right; }

contract AbiHashing {
    function scalar(uint128 a, address b, bytes32 c, bool d) external pure returns (bytes32) {
        return keccak256(abi.encode(a, b, c, d));
    }

    function empty() external pure returns (bytes32) {
        return keccak256(abi.encode());
    }

    function distinct(uint256 a, uint256 b) external pure returns (bytes32, bytes32) {
        bytes32 left = keccak256(abi.encode(a));
        bytes32 right = keccak256(abi.encode(b));
        return (left, right);
    }

    function composed(uint256 a, uint256 b) external pure returns (bytes32) {
        bytes32 left = keccak256(abi.encode(a));
        bytes32 right = keccak256(abi.encode(b));
        return keccak256(abi.encode(left, right));
    }

    function marketMemory(Market memory market, uint256 flag) external pure returns (bytes32) {
        require(flag != 0, "first");
        return keccak256(abi.encode(market));
    }

    function marketCalldata(Market calldata market, uint256 flag) external pure returns (bytes32) {
        require(flag != 0, "first");
        return keccak256(abi.encode(market));
    }

    function staticRoot(HashStatic calldata value) external pure returns (bytes32) {
        return keccak256(abi.encode(value));
    }

    function arraysMemory(HashArrays memory value) external pure returns (bytes32) {
        return keccak256(abi.encode(value));
    }

    function arraysCalldata(HashArrays calldata value) external pure returns (bytes32) {
        return keccak256(abi.encode(value));
    }
    function packedScalars(uint8 a, address b, uint256 c, bytes32 d, bool e) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(a, b, c, d, e));
    }

    function idMarket(Market memory market) external pure returns (bytes32) {
        return IdLib.toId(market);
    }

    function prefix0(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"", abi.encode(value)));
    }

    function prefix1(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"03", abi.encode(value)));
    }

    function prefix11(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b4249", abi.encode(value)));
    }

    function prefix31(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5", abi.encode(value)));
    }

    function prefix32(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dc", abi.encode(value)));
    }

    function prefix33(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3", abi.encode(value)));
    }

    function prefix63(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5", abi.encode(value)));
    }

    function prefix64(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bc", abi.encode(value)));
    }

    function prefix65(uint256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dce3eaf1f8ff060d141b222930373e454c535a61686f767d848b9299a0a7aeb5bcc3", abi.encode(value)));
    }

    bytes32 private storedDigest;
    event Hashed(bytes32 indexed value);

    function storeDigest(uint256 value, uint256 flag) external returns (bytes32) {
        bytes32 digest = keccak256(abi.encodePacked(uint8(0xff), abi.encode(value)));
        storedDigest = digest;
        emit Hashed(digest);
        require(flag != 0, "rollback");
        return digest;
    }

    function readDigest() external view returns (bytes32) {
        return storedDigest;
    }
}
