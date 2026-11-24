// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface ICheckedRelay {
    function echo(uint256 left, uint256 right) external view returns (uint256);
    function echoBytes(bytes calldata data, uint256 value) external view returns (uint256);
    function notify(uint256 left, uint256 right) external;
}

library ScalarCast {
    error ValueTooWide(uint256 value);

    function toUint104(uint256 value) internal pure returns (uint104) {
        require(value <= type(uint104).max, ValueTooWide(value));
        return uint104(value);
    }
}

/// External-call, event and custom-error arguments whose expressions can revert or read
/// storage. solc evaluates an argument list left to right before ABI-encoding the call or
/// the log, so a guard in one argument reverts before any later argument runs.
contract CheckedArgumentFixture {
    using ScalarCast for uint256;

    struct Entry {
        uint256 weight;
    }

    uint256 internal total;
    Entry internal entry;

    error FieldTooSmall(uint256 field);
    event Measured(uint256 sum, uint256 difference);

    /// A checked library downcast and a checked subtraction inside a staticcall's arguments.
    function callChecked(address target, uint256 value, uint256 other) external returns (uint256) {
        uint256 result = ICheckedRelay(target).echo(uint256(value.toUint104()), other - 1);
        total = result;
        return result;
    }

    /// Checked arithmetic inside an external call's arguments: the overflow must revert
    /// before the call executes.
    function callOverflow(address target, uint256 value) external returns (uint256) {
        uint256 result = ICheckedRelay(target).echo(value + 1, value);
        total = result;
        return result;
    }

    /// A checked library downcast beside a dynamic bytes parameter, which takes the encoded
    /// argument path rather than the scalar word path.
    function callDynamic(address target, bytes calldata data, uint256 value) external returns (uint256) {
        uint256 result = ICheckedRelay(target).echoBytes(data, uint256(value.toUint104()));
        total = result;
        return result;
    }

    /// A checked library downcast and checked addition inside a void external call's arguments.
    function callVoid(address target, uint256 value, uint256 other) external {
        ICheckedRelay(target).notify(uint256(value.toUint104()), other + 1);
    }

    /// Checked scalar arithmetic and a storage member read as event arguments.
    function emitMeasured(uint256 left, uint256 right) external {
        emit Measured(left + right, entry.weight - left);
    }

    /// A checked expression and a storage member read as a custom-error argument.
    function revertField(uint256 floorValue) external view {
        revert FieldTooSmall(entry.weight + floorValue);
    }

    /// A named custom-error argument reading a storage struct member.
    function revertNamedField() external view {
        revert FieldTooSmall({field: entry.weight});
    }

    /// Seed the storage struct member for concrete execution checks.
    function seedWeight(uint256 w) external {
        entry.weight = w;
    }

    function read() external view returns (uint256, uint256) {
        return (total, entry.weight);
    }
}
