// SPDX-License-Identifier: MIT
pragma solidity >=0.8.34 <0.9.0;

interface INearMissOracle {
    function peekBytes32() external view returns (bytes32);
    function peekUint() external view returns (uint256);
    function deployWord(bytes memory initPayload, bytes32 salt) external returns (address);
}

type WrappedUint is uint256;

function eqWrappedStateful(WrappedUint a, WrappedUint b) pure returns (bool) {
    return WrappedUint.unwrap(a) == WrappedUint.unwrap(b);
}

using {eqWrappedStateful as ==} for WrappedUint global;

/// Near-miss shapes outside the admitted stateful comparison and struct-mapping RHS slice (#2976).
contract StatefulComparisonStructMapRhsRejections {
    struct Bucket {
        mapping(bytes32 => uint256) entries;
        uint256[] dynValues;
        uint256[4] fixedValues;
    }

    mapping(bytes32 => Bucket) internal buckets;
    mapping(bytes32 => uint256) internal flatEntries;
    uint256 internal counter;

    function _packKey(address targetAddr, bytes4 sel) private pure returns (bytes32) {
        return bytes32(bytes20(targetAddr)) | (bytes32(sel) >> 160);
    }

    function _bump() internal returns (uint256) {
        counter = counter + 1;
        return counter;
    }

    function _bumpWrapped() internal returns (WrappedUint) {
        counter = counter + 1;
        return WrappedUint.wrap(counter);
    }

    function _writeMem(uint256[2] memory arr) internal returns (uint256) {
        counter = counter + 1;
        arr[0] = counter;
        return arr[0];
    }

    function _writeMemPure(uint256[2] memory arr) internal pure returns (uint256) {
        arr[0] = arr[0] + 1;
        return arr[0];
    }

    function arithmeticWithStatefulOperand(uint256 x) external returns (uint256) {
        return _bump() + x;
    }

    function bitwiseWithStatefulOperand(uint256 x) external returns (uint256) {
        return x | _bump();
    }

    function userDefinedEqWithStatefulOperand(uint256 x) external returns (bool) {
        return WrappedUint.wrap(x) == _bumpWrapped();
    }

    function comparisonWithAssignmentOperand(uint256 x) external returns (bool) {
        uint256 y = x;
        return (y = x + 1) == _bump();
    }

    function comparisonWithMemoryWriteHazard(uint256 x) external returns (bool) {
        uint256[2] memory arr;
        arr[0] = x;
        return arr[0] == _writeMem(arr);
    }

    function comparisonWithPureMemoryWriteHazard(uint256 x) external pure returns (bool) {
        uint256[2] memory arr;
        arr[0] = x;
        return arr[0] == _writeMemPure(arr);
    }

    function flatMappingComputedKeyInterfaceRhs(address oracle, address targetAddr, bytes4 sel)
        external
    {
        flatEntries[_packKey(targetAddr, sel)] = INearMissOracle(oracle).peekUint();
    }

    function structMappingCompoundInterfaceRhs(
        address oracle,
        bytes32 bucketKey,
        address targetAddr,
        bytes4 sel
    ) external {
        buckets[bucketKey].entries[_packKey(targetAddr, sel)] += INearMissOracle(oracle).peekUint();
    }

    function structMappingCompoundStatefulRhs(bytes32 bucketKey, address targetAddr, bytes4 sel)
        external
    {
        buckets[bucketKey].entries[_packKey(targetAddr, sel)] += _bump();
    }

    function structMappingInterfaceCallInKey(address oracle, bytes32 bucketKey) external {
        buckets[bucketKey].entries[INearMissOracle(oracle).peekBytes32()] = 1;
    }

    function structMappingAssignmentInRhs(bytes32 bucketKey, address targetAddr, bytes4 sel)
        external
        returns (uint256)
    {
        uint256 local = 0;
        buckets[bucketKey].entries[_packKey(targetAddr, sel)] = (local = 9);
        return local;
    }

    function structDynamicArrayStatefulRhs(bytes32 bucketKey) external {
        buckets[bucketKey].dynValues[0] = _bump();
    }

    function structFixedArrayInterfaceRhs(address oracle, bytes32 bucketKey) external {
        buckets[bucketKey].fixedValues[0] = INearMissOracle(oracle).peekUint();
    }

    function valueCallBeforeStructMappingWrite(address target, bytes32 bucketKey, bytes32 entryKey)
        external
    {
        (bool ok, ) = target.call{value: 1}("");
        buckets[bucketKey].entries[entryKey] = ok ? 1 : 0;
    }
}
