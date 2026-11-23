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

contract ConcatBesideC is NamedBase {
    function digest(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(x, string.concat(_name(), _name())));
    }
}

contract StorageBesideC is NamedBase {
    function digest(uint256 x) external view returns (bytes32) {
        return keccak256(abi.encode(label, x, _name()));
    }
}

// A string literal as event data for a `bytesN` parameter: solc encodes the static `bytes1`
// word, the event data encoder (by argument types) would encode a dynamic `string`.
contract EventLiteralFixedBytesC {
    event Tagged(bytes1 fields, string note);

    function tag(string memory note) external {
        emit Tagged(hex"0f", note);
    }
}

interface ITagged {
    function tagged(bytes1 fields) external view returns (uint256);
}

// A string literal for a `bytesN` parameter of an all-static typed interface call.
contract InterfaceLiteralFixedBytesC {
    function probe(address target) external view returns (uint256) {
        return ITagged(target).tagged(hex"0f");
    }
}
