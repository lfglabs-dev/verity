// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IStatefulTarget {
    function poke(uint256 x) external returns (uint256);
}

// Encoding forms that stay rejected beside a state-changing helper argument.
abstract contract Counter {
    uint256 internal count;
    bytes internal blob;

    struct Pair {
        uint256 a;
        uint256 b;
    }

    Pair internal pair;

    function _bump() internal returns (uint256) {
        count += 1;
        return count;
    }
}

contract PackedC is Counter {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encodePacked(x, _bump()));
    }
}

contract SelectorC is Counter {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encodeWithSelector(IStatefulTarget.poke.selector, x, _bump()));
    }
}

contract DynamicC is Counter {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(blob, x, _bump()));
    }
}

contract StructC is Counter {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(x, _bump(), pair));
    }
}

contract ExternalC is Counter {
    IStatefulTarget internal target;

    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(_bump(), target.poke(x)));
    }
}

contract NestedPackedC is Counter {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encodePacked(keccak256(abi.encode(_bump())), x));
    }
}
