// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

struct Leg {
    address token;
    uint256 weight;
}

struct Spec {
    uint256 tag;
    address owner;
    Leg[] legs;
    uint256 deadline;
}

/// SSTORE2-style code storage: the creation code is an 11-byte prefix that
/// returns everything after itself as the runtime code of the new account.
library CodeStore {
    error DeploymentFailed();

    bytes constant PREFIX = hex"600b380380600b5f395ff3";

    function store(Spec memory spec, bytes32 salt) internal returns (address deployed) {
        bytes memory code = abi.encodePacked(PREFIX, abi.encode(spec));
        assembly ("memory-safe") {
            deployed := create2(0, add(code, 0x20), mload(code), salt)
        }
        require(deployed != address(0), DeploymentFailed());
    }
}

contract Create2BytecodeAndStructEmitSequence {
    event Stored(Spec spec, bytes32 indexed id);
    event LegStored(address indexed pointer, Leg leg, uint256 indexed index);

    mapping(bytes32 => uint256) private created;
    uint256 private total;

    function create(Spec memory spec) external returns (bytes32 id) {
        id = keccak256(abi.encode(spec));
        if (created[id] == 0) {
            created[id] = 1;
            CodeStore.store(spec, 0);
            emit Stored(spec, id);
        }
    }

    function storeAt(Spec memory spec, bytes32 salt) external returns (address) {
        address deployed = CodeStore.store(spec, salt);
        total += 1;
        return deployed;
    }

    function storeLeg(Leg memory leg, uint256 index) external returns (address pointer) {
        bytes memory code = bytes.concat(hex"600b380380600b5f395ff3", abi.encode(leg));
        assembly {
            pointer := create2(0, add(code, 32), mload(code), index)
        }
        emit LegStored(pointer, leg, index);
    }

    function count() external view returns (uint256) {
        return total;
    }
}
