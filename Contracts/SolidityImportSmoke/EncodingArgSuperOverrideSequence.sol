// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IEncodingArgTarget {
    function accept(bytes32 left, uint256 right) external;
}

// Multi-level C3 diamond (`SequenceFixture -> EncodingSuperRight -> EncodingSuperLeft ->
// EncodingSuperRoot`) with a single storage slot. `SequenceFixture.prefix` forwards to
// `super.prefix()`, and `change` passes both virtual and `super` calls to `abi.encodePacked`,
// `abi.encode`, `abi.encodeWithSelector`, and `abi.encodeCall`.
contract EncodingSuperRoot {
    uint256 internal saved;

    function prefix() internal virtual view returns (bytes32) {
        if (block.chainid == 1) {
            return bytes32(saved ^ 0x55);
        }
        return keccak256(abi.encode(block.chainid, address(this)));
    }

    function step(uint256 x) internal virtual pure returns (uint256) {
        return x ^ 0x1111;
    }
}

contract EncodingSuperLeft is EncodingSuperRoot {
    function prefix() internal virtual override view returns (bytes32) {
        return bytes32(uint256(super.prefix()) ^ 0xa1);
    }

    function step(uint256 x) internal virtual override pure returns (uint256) {
        return (super.step(x) << 1) ^ 0x2222;
    }
}

contract EncodingSuperRight is EncodingSuperRoot {
    function prefix() internal virtual override view returns (bytes32) {
        return bytes32(uint256(super.prefix()) ^ 0xb200);
    }

    function step(uint256 x) internal virtual override pure returns (uint256) {
        return super.step(x) ^ 0x3333;
    }
}

contract SequenceFixture is EncodingSuperLeft, EncodingSuperRight {
    function prefix()
        internal
        override(EncodingSuperLeft, EncodingSuperRight)
        view
        returns (bytes32)
    {
        return super.prefix();
    }

    function step(uint256 x)
        internal
        override(EncodingSuperLeft, EncodingSuperRight)
        pure
        returns (uint256)
    {
        return super.step(x) ^ 0x4444;
    }

    function change(uint256 next) external returns (uint256) {
        bytes32 digest;
        if (next % 4 == 0) {
            digest = keccak256(abi.encodePacked("\x19\x01", prefix(), bytes32(next)));
        } else if (next % 4 == 1) {
            digest = keccak256(abi.encode(prefix(), super.step(next), EncodingSuperRoot.step(next)));
        } else if (next % 4 == 2) {
            digest = keccak256(abi.encodeWithSelector(IEncodingArgTarget.accept.selector, prefix(), super.step(next)));
        } else {
            digest = keccak256(abi.encodeCall(IEncodingArgTarget.accept, (prefix(), super.step(next))));
        }
        saved = uint256(digest);
        return saved;
    }

    function fail() external {
        saved = 77;
        revert();
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
