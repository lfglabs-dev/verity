// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract EnumFeatureReference {
    enum Status { Pending, Active, Closed }

    Status internal status;
    mapping(uint256 => Status) internal statuses;

    function identity(Status value) external pure returns (Status) { return value; }
    function active() external pure returns (Status) { return Status.Active; }
    function castStatus(uint256 value) external pure returns (Status) { return Status(value); }
    function setStatus(Status value) external { status = value; }
    function getStatus() external view returns (Status) { return status; }
    function setStatusAt(uint256 key, Status value) external { statuses[key] = value; }
    function getStatusAt(uint256 key) external view returns (Status) { return statuses[key]; }
}

contract EnumFeatureTest is Test, YulTestBase {
    address internal enumFeature;
    EnumFeatureReference internal referenceContract;

    function setUp() public {
        enumFeature = deployCompiledVerityModule(
            "Contracts.Smoke.EnumFeatureTest",
            "MacroEnumUsage",
            _smokeYulDir()
        );
        referenceContract = new EnumFeatureReference();
    }

    function _assertCallParity(bytes memory payload) internal {
        (bool yulSuccess, bytes memory yulData) = enumFeature.call(payload);
        (bool refSuccess, bytes memory refData) = address(referenceContract).call(payload);
        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "return/revert payload mismatch");
    }

    function testMembersParamsReturnsAndCastParity() public {
        _assertCallParity(abi.encodeWithSignature("active()"));
        _assertCallParity(abi.encodeWithSignature("identity(uint8)", uint8(2)));
        _assertCallParity(abi.encodeWithSignature("identity(uint8)", uint8(3)));
        _assertCallParity(abi.encodeWithSignature("castStatus(uint256)", 0));
        _assertCallParity(abi.encodeWithSignature("castStatus(uint256)", 2));
        _assertCallParity(abi.encodeWithSignature("castStatus(uint256)", 3));
        _assertCallParity(abi.encodeWithSignature("castStatus(uint256)", type(uint256).max));
        _assertCallParity(abi.encodeWithSelector(bytes4(keccak256("identity(uint8)")), uint256(0x100)));
    }

    function testStorageAndMappingParity() public {
        _assertCallParity(abi.encodeWithSignature("setStatus(uint8)", uint8(2)));
        _assertCallParity(abi.encodeWithSignature("getStatus()"));
        _assertCallParity(abi.encodeWithSignature("setStatusAt(uint256,uint8)", 7, uint8(1)));
        _assertCallParity(abi.encodeWithSignature("getStatusAt(uint256)", 7));
        assertEq(vm.load(enumFeature, bytes32(uint256(0))), vm.load(address(referenceContract), bytes32(uint256(0))));
        bytes32 mapSlot = keccak256(abi.encode(uint256(7), uint256(1)));
        assertEq(vm.load(enumFeature, mapSlot), vm.load(address(referenceContract), mapSlot));
    }
}
