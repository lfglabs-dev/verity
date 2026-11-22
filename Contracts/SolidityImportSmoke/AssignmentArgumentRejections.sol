// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Assignment and increment arguments that keep a located rejection. Each contract has
// two state variables so that only the construct under test is rejected.

contract DynamicC {
    uint256 internal n;
    uint256 internal other;
    function digest(bytes memory b) external returns (bytes32) {
        return keccak256(abi.encode(b, n, n++));
    }
}

contract HashedDynamicC {
    uint256 internal n;
    uint256 internal other;
    function digest(bytes memory b) external returns (bytes32) {
        return keccak256(abi.encode(b, n, keccak256(abi.encode(n++))));
    }
}

contract ConcatC {
    uint256 internal n;
    uint256 internal other;
    function digest(uint256) external returns (bytes32) {
        return keccak256(bytes.concat(abi.encode(n++), abi.encode(n)));
    }
}

contract PackedC {
    uint256 internal n;
    uint256 internal other;
    function digest(uint256) external returns (bytes32) {
        return keccak256(abi.encodePacked(n, n++));
    }
}

contract MappingAssignC {
    uint256 internal other;
    mapping(uint256 => uint256) internal m;
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(m[x], m[x] = 9, m[x]));
    }
}

contract CompoundC {
    uint256 internal n;
    uint256 internal other;
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(n, n += x, n));
    }
}

contract StructC {
    struct Pair { uint256 a; uint256 b; }
    uint256 internal n;
    uint256 internal other;
    function digest(uint256 x) external returns (bytes32) {
        Pair memory pair = Pair(x, x);
        return keccak256(abi.encode(pair, n++));
    }
}

contract CallMappingAssignC {
    uint256 internal other;
    mapping(uint256 => uint256) internal m;
    function mix(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) {
        return a ^ b ^ c;
    }
    function digest(uint256 x) external returns (uint256) {
        return mix(m[x], m[x] = 9, m[x]);
    }
}

contract CallComputedKeyC {
    uint256 internal other;
    mapping(uint256 => uint256) internal m;
    function mix(uint256 a, uint256 b) internal pure returns (uint256) {
        return a ^ b;
    }
    function digest(uint256 x) external returns (uint256) {
        return mix(x, m[x + 1]++);
    }
}

// Positive control: a `bytes calldata` and an enum sibling beside `nonce++` in an internal call
// of a public function, read before the increment.
contract CalldataSiblingC {
    enum Op { Call, DelegateCall }
    uint256 public nonce;
    uint256 internal other;
    function hashOf(address to, bytes calldata data, Op op, uint256 n) public view returns (bytes32) {
        return keccak256(abi.encode(to, keccak256(data), op, n, other));
    }
    function digest(address to, bytes calldata data, Op op) external returns (bytes32) {
        return hashOf(to, data, op, nonce++);
    }
}
