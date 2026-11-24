// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Emptiness tests of the executing contract's own code (`address(this).code.length == 0`, the
// initializer / constructor guard): `EXTCODESIZE(ADDRESS())` against zero. The executing
// account has code on both EVM routes at runtime and none during construction (including a
// delegatecall from a constructor), so the test agrees across routes; the length itself differs
// between the source and compiled bytecode and stays rejected (SyntheticCodeLengthChecks.lean).
contract SyntheticCodeLength {
    uint256 private initialized;

    error AlreadyInitialized();

    function _isConstructing() private view returns (bool) {
        return address(this).code.length == 0;
    }

    function isConstructing() external view returns (bool) {
        return address(this).code.length == 0;
    }

    function hasCode() external view returns (bool, bool, bool) {
        return (address(this).code.length > 0, 0 < address(this).code.length,
            address(this).code.length != 0);
    }

    function mirrored() external view returns (bool, bool) {
        return (0 == address(this).code.length, address(this).code.length <= 0);
    }

    function initialize(uint256 value) external {
        if (initialized != 0 && !_isConstructing()) revert AlreadyInitialized();
        initialized = value;
    }

    function guarded(uint256 value) external returns (uint256) {
        require(address(this).code.length != 0, "constructing");
        initialized = initialized + value;
        return initialized;
    }
}

// The length value itself and other self-code reads stay rejected.
contract SyntheticCodeLengthUnsupported {
    function selfLength() external view returns (uint256) {
        return address(this).code.length;
    }

    function selfLengthCompare() external view returns (bool) {
        return address(this).code.length > 1;
    }

    function selfAlias() external view returns (bool) {
        address self = address(this);
        return self.code.length == 0;
    }
}
