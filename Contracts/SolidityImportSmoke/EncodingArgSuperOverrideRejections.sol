// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Model-equivalence pair: 3-level C3 `super.sep()` chain vs flat helper with no `super`.
contract ChainSuperA {
    function sep() internal virtual view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, address(this)));
    }
}

contract ChainSuperB is ChainSuperA {
    function sep() internal virtual override view returns (bytes32) {
        return bytes32(uint256(super.sep()) ^ 0x55);
    }
}

contract ChainSuperC is ChainSuperB {
    function sep() internal override view returns (bytes32) {
        return super.sep();
    }

    function digest(bytes32 item) external view returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", sep(), item));
    }
}

contract ChainPlainC {
    function sepA() internal view returns (bytes32) {
        return keccak256(abi.encode(block.chainid, address(this)));
    }

    function sepB() internal view returns (bytes32) {
        return bytes32(uint256(sepA()) ^ 0x55);
    }

    function sep() internal view returns (bytes32) {
        return sepB();
    }

    function digest(bytes32 item) external view returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", sep(), item));
    }
}

// 1. Multi-level `super` chain whose base uses `require(...)`.
contract RevertChainA {
    function sep(uint256 x) internal virtual pure returns (bytes32) {
        require(x != 0, "zero");
        return bytes32(x);
    }
}

contract RevertChainB is RevertChainA {
    function sep(uint256 x) internal virtual override pure returns (bytes32) {
        return super.sep(x);
    }
}

contract RevertChainC is RevertChainB {
    function sep(uint256 x) internal override pure returns (bytes32) {
        return super.sep(x);
    }

    function digest(uint256 x, bytes32 item) external pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", sep(x), item));
    }
}

// 2. C3 diamond where `DiamondRight.sep`'s `referencedDeclaration` points to pure
// `DiamondRoot.sep`, but `DiamondLeaf`'s C3 order routes `DiamondRight`'s `super.sep()`
// through reverting `DiamondLeft.sep`.
contract DiamondRoot {
    function sep(uint256 x) internal virtual pure returns (bytes32) {
        return bytes32(x ^ 1);
    }
}

contract DiamondLeft is DiamondRoot {
    error DiamondBlocked();

    function sep(uint256 x) internal virtual override pure returns (bytes32) {
        if (x == 0) {
            revert DiamondBlocked();
        }
        return bytes32(x);
    }
}

contract DiamondRight is DiamondRoot {
    function sep(uint256 x) internal virtual override pure returns (bytes32) {
        return super.sep(x);
    }
}

contract DiamondLeaf is DiamondLeft, DiamondRight {
    function sep(uint256 x) internal override(DiamondLeft, DiamondRight) pure returns (bytes32) {
        return super.sep(x);
    }

    function digest(uint256 x, bytes32 item) external pure returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", sep(x), item));
    }
}

// 3 & 4. Reverting base overridden by a non-reverting derived implementation: direct
// `super.sep(x)` and qualified `DirectRevertBase.sep(x)` still call the reverting base.
contract DirectRevertBase {
    function sep(uint256 x) internal virtual pure returns (bytes32) {
        if (x == 0) {
            revert();
        }
        return bytes32(x);
    }
}

contract DirectRevertDerived is DirectRevertBase {
    function sep(uint256 x) internal override pure returns (bytes32) {
        return bytes32(x ^ 7);
    }

    function viaSuper(uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encode(super.sep(x)));
    }

    function viaQualified(uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encode(DirectRevertBase.sep(x)));
    }
}

// 5. Stateful base overridden by a `pure` implementation: `super.bump()` writes storage.
contract StatefulSuperBase {
    uint256 internal counter;

    function bump() internal virtual returns (uint256) {
        counter += 1;
        return counter;
    }
}

contract StatefulSuperDerived is StatefulSuperBase {
    function bump() internal override pure returns (uint256) {
        return 1;
    }

    function encodeDynamic(bytes memory payload) external returns (bytes32) {
        return keccak256(abi.encode(payload, super.bump()));
    }
}
