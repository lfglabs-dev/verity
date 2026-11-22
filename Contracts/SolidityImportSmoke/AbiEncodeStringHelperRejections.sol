// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// `string` helper arguments of `abi.encode` that stay located rejections.
abstract contract NamedBase {
    error EmptyName();

    string internal label;
    uint256 internal count;

    function _name() internal view returns (string memory) {
        if (bytes(label).length == 0) revert EmptyName();
        return label;
    }

    function _bump() internal returns (uint256) {
        count += 1;
        return count;
    }

    function _countedName() internal returns (string memory) {
        count += 1;
        return label;
    }

    function _checkedCount() internal view returns (uint256) {
        if (count == 0) revert EmptyName();
        return count;
    }
}

contract StatefulStringC is NamedBase {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(_countedName(), x));
    }
}

contract StringBesideStatefulC is NamedBase {
    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(_name(), x, _bump()));
    }
}

contract StringBesideCalldataC is NamedBase {
    function digest(bytes calldata data) external view returns (bytes32) {
        return keccak256(abi.encode(data, _name()));
    }
}

contract StringBesideRevertingScalarC is NamedBase {
    function digest(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(_name(), x, _checkedCount()));
    }
}
