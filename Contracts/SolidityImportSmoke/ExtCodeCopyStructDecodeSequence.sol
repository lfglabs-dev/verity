// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

struct Leg {
    address token;
    uint96 weight;
    bool active;
}

struct Spec {
    uint256 tag;
    address owner;
    Leg[] legs;
    uint64[] marks;
    uint256 deadline;
}

/// SSTORE2-style code storage: the creation code is an 11-byte prefix that
/// returns everything after itself as the runtime code of the new account.
library CodeStore {
    error DeploymentFailed();

    bytes constant PREFIX = hex"600b380380600b5f395ff3";

    function write(Spec memory spec, bytes32 salt) internal returns (address pointer) {
        bytes memory code = abi.encodePacked(PREFIX, abi.encode(spec));
        assembly ("memory-safe") {
            pointer := create2(0, add(code, 0x20), mload(code), salt)
        }
        require(pointer != address(0), DeploymentFailed());
    }
}

contract ExtCodeCopyStructDecodeSequence {
    error Missing();

    mapping(bytes32 => bytes32) private ids;
    uint256 private total;

    function store(Spec memory spec) external returns (bytes32 id) {
        bytes32 key = keccak256(abi.encode(spec));
        id = ids[key];
        if (id == 0) {
            id = bytes32(uint256(uint160(CodeStore.write(spec, key))));
            ids[key] = id;
            total += 1;
        }
    }

    function storeRaw(bytes calldata payload, bytes32 salt) external returns (address pointer) {
        bytes memory code = bytes.concat(hex"600b380380600b5f395ff3", payload);
        assembly {
            pointer := create2(0, add(code, 32), mload(code), salt)
        }
    }

    function load(bytes32 id) external view returns (Spec memory) {
        require(total > 0, Missing());
        address pointer = address(uint160(uint256(id)));
        return abi.decode(pointer.code, (Spec));
    }

    function summary(address pointer) external view returns (address, uint256, uint256) {
        Spec memory spec = abi.decode(pointer.code, (Spec));
        return (spec.owner, spec.legs.length, spec.marks.length);
    }

    function echo(Spec memory spec) external pure returns (Spec memory) {
        return spec;
    }
}
