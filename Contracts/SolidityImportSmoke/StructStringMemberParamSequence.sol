// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `string` members of ABI-decoded struct parameters (#2711): `string` and
// `bytes` share the dynamic byte-array ABI encoding, so a `string` member is
// decoded, bounds-checked and read exactly like a `bytes` member, in memory
// (eager copy) and calldata (lazy) structs. Also covered: a `string` member
// written to a `string` storage variable (`Pool.configureEModeCategory`'s
// shape) and a `string` inside a nested dynamic struct.
contract SequenceFixture {
    struct CategoryConfig {
        uint16 ltv;
        bool isolated;
        string label;
    }

    struct Tagged {
        string name;
        uint256 weight;
        bytes payload;
    }

    struct Outer {
        uint256 id;
        Tagged tag;
    }

    uint256 private stored;
    string private storedLabel;

    // The issue's shape: only a scalar sibling of the `string` member is read.
    function configure(CategoryConfig memory cfg) external returns (uint256) {
        stored = cfg.ltv;
        return cfg.isolated ? 1 : 0;
    }

    function labelLength(CategoryConfig memory cfg) external pure returns (uint256) {
        return bytes(cfg.label).length;
    }

    function labelHash(CategoryConfig memory cfg) external pure returns (bytes32) {
        return keccak256(bytes(cfg.label));
    }

    function labelLengthCalldata(CategoryConfig calldata cfg) external pure returns (uint256) {
        return bytes(cfg.label).length + cfg.ltv;
    }

    function labelHashCalldata(CategoryConfig calldata cfg) external pure returns (bytes32) {
        return keccak256(bytes(cfg.label));
    }

    function taggedDigest(Tagged memory t) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(bytes(t.name), t.weight, t.payload));
    }

    function storeLabel(CategoryConfig memory cfg) external {
        storedLabel = cfg.label;
    }

    function storeLabelCalldata(CategoryConfig calldata cfg) external {
        storedLabel = cfg.label;
    }

    function readLabel() external view returns (string memory) {
        return storedLabel;
    }

    function nestedName(Outer memory o) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(o.id, bytes(o.tag.name), o.tag.weight));
    }

    function nestedNameCalldata(Outer calldata o) external pure returns (uint256) {
        return bytes(o.tag.name).length + o.id;
    }

    function change(uint256 x) external {
        stored = x;
    }

    function fail() external pure {
        revert("fail");
    }

    function read() external view returns (uint256) {
        return stored;
    }
}
