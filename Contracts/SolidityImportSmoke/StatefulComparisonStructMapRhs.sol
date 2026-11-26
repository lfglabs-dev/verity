// SPDX-License-Identifier: MIT
pragma solidity >=0.8.34 <0.9.0;

interface IWordDeployer {
    function deployWord(bytes memory initPayload, bytes32 salt) external returns (address);
}

interface ICallbackTarget {
    function invoke() external;
}

library LinkedConfigLib {
    function storeLinked(address target, uint256 tag) external returns (uint256) {
        address deployed = IWordDeployer(target).deployWord(abi.encode(tag), bytes32(0));
        return uint160(deployed);
    }

    function invokeLinked(address hook, uint256 tag) external returns (uint256) {
        ICallbackTarget(hook).invoke();
        return tag + 1000;
    }
}

/// Construct-generic fixture for stateful external, internal, and linked-library calls:
/// (a) as an operand of a binary comparison (`==`, `!=`, `<`, `<=`, `>`, `>=`), and
/// (b) as the right-hand side of a storage-struct mapping element write (`buckets[k].entries[m] = ...`).
contract StatefulComparisonStructMapRhs {
    event Step(uint256 code, uint256 value);
    event EntryStored(bytes32 indexed bucketKey, bytes32 indexed entryKey, uint256 value);

    struct Bucket {
        mapping(bytes32 => uint256) entries;
        mapping(uint256 => mapping(bytes32 => uint256)) nested;
    }

    mapping(bytes32 => Bucket) internal buckets;
    bytes32 public curBucket;
    address public curTarget;
    uint256 public stored;
    uint256 public stamp;

    function _packKey(address targetAddr, bytes4 sel) private pure returns (bytes32) {
        return bytes32(bytes20(targetAddr)) | (bytes32(sel) >> 160);
    }

    function _deployChecked(address target, bytes memory payload, address expected)
        internal
        returns (uint256)
    {
        address pointer = expected;
        pointer = address(uint160(pointer) ^ 0);
        assert(pointer == IWordDeployer(target).deployWord(payload, bytes32(0)));
        return uint160(pointer);
    }

    function _deployDirect(address target, bytes memory payload) internal returns (uint256) {
        address deployed = IWordDeployer(target).deployWord(payload, bytes32(0));
        return uint160(deployed);
    }

    function _stepWord(uint256 code, uint256 newStored, uint256 ret) internal returns (uint256) {
        emit Step(code, newStored);
        stored = newStored;
        return ret;
    }

    function _invokeAndReturn(address hook, uint256 ret) internal returns (uint256) {
        ICallbackTarget(hook).invoke();
        return ret;
    }

    function _bumpCounter() internal returns (uint256) {
        stamp = stamp * 10 + 7;
        emit Step(70, stamp);
        return stamp;
    }

    function _outerKeyStep(bytes32 bucketKey) internal returns (bytes32) {
        stamp = stamp * 10 + 1;
        stored = stored + 100;
        emit Step(10, stamp);
        return bucketKey;
    }

    function _innerKeyStep(address targetAddr, bytes4 sel) internal returns (bytes32) {
        stamp = stamp * 10 + 2;
        emit Step(20, stamp);
        return _packKey(targetAddr, sel);
    }

    function _panicOuter(uint256 divisor, bytes32 bucketKey) private pure returns (bytes32) {
        uint256 q = 100 / divisor;
        return bytes32(q) ^ bucketKey;
    }

    function _panicInner(uint256 x, bytes32 entryKey) private pure returns (bytes32) {
        uint256 d = x - 1;
        return bytes32(d) ^ entryKey;
    }

    /// Shape (a): trailing external call inside `assert(pointer == deployWord(...))`.
    function assertDeployMatch(address target, bytes memory payload, address expected)
        external
        returns (uint256)
    {
        return _deployChecked(target, payload, expected);
    }

    /// Shape (a): comparisons across `==`, `!=`, `<`, `<=`, `>`, `>=` whose evaluation order
    /// differs between via-IR (left-to-right) and legacy (right-to-left).
    function compareCallAndState(address target, uint256 mode, uint256 arg, address expected)
        external
        returns (uint256)
    {
        bool ok;
        if (mode == 0) {
            stored = 5;
            ok = (stored == _stepWord(2, 9, 5));
        } else if (mode == 1) {
            stored = 5;
            ok = (_stepWord(1, 9, 5) == stored);
        } else if (mode == 2) {
            ok = (_stepWord(1, 11, arg) == _stepWord(2, 22, arg));
        } else if (mode == 3) {
            stored = 5;
            ok = (stored < _stepWord(2, 10, 6));
        } else if (mode == 4) {
            stored = 5;
            ok = (_stepWord(1, 10, 8) <= stored);
        } else if (mode == 5) {
            ok = (address(uint160(100 / arg)) == IWordDeployer(target).deployWord(abi.encode(arg), bytes32(0)));
        } else if (mode == 6) {
            ok = (IWordDeployer(target).deployWord(abi.encode(arg), bytes32(0)) != address(uint160(100 / arg)));
        } else if (mode == 7) {
            ok = (LinkedConfigLib.storeLinked(target, arg) >= uint160(expected));
        } else if (mode == 8) {
            stored = 5;
            ok = (stored == _invokeAndReturn(target, 5));
        } else {
            stored = 5;
            ok = (_invokeAndReturn(target, 5) > stored);
        }
        return (ok ? 100000 : 0) + stored;
    }

    /// Shape (b): struct-mapping write with direct key and stateful internal helper calling external target.
    function setDirectKeyInternal(
        address target,
        bytes32 bucketKey,
        bytes32 entryKey,
        bytes memory payload
    ) external {
        buckets[bucketKey].entries[entryKey] = _deployDirect(target, payload);
        emit EntryStored(bucketKey, entryKey, buckets[bucketKey].entries[entryKey]);
    }

    /// Shape (b): struct-mapping write with pure computed key and linked external library call.
    function setComputedKeyLinked(
        address target,
        bytes32 bucketKey,
        address targetAddr,
        bytes4 sel,
        uint256 tag
    ) external {
        bytes32 computed = _packKey(targetAddr, sel);
        buckets[bucketKey].entries[_packKey(targetAddr, sel)] = LinkedConfigLib.storeLinked(target, tag);
        emit EntryStored(bucketKey, computed, buckets[bucketKey].entries[computed]);
    }

    /// Shape (b): struct-mapping write with side-effecting key helpers, competing panics, and 2D struct mapping.
    function setSideEffectKeysOrder(
        address target,
        uint256 mode,
        bytes32 bucketKey,
        address targetAddr,
        bytes4 sel,
        uint256 aux
    ) external {
        stamp = 3;
        if (mode == 0) {
            buckets[_outerKeyStep(bucketKey)].entries[_innerKeyStep(targetAddr, sel)] =
                LinkedConfigLib.storeLinked(target, aux);
        } else if (mode == 1) {
            buckets[_panicOuter(aux, bucketKey)].entries[_panicInner(0, bytes32(uint256(2)))] =
                uint160(IWordDeployer(target).deployWord(abi.encode(aux), bytes32(0)));
        } else if (mode == 2) {
            buckets[bucketKey].nested[aux][_innerKeyStep(targetAddr, sel)] =
                _deployDirect(target, abi.encode(aux));
        } else {
            stored = aux;
            buckets[_outerKeyStep(bucketKey)].entries[_innerKeyStep(targetAddr, sel)] = stored;
        }
    }

    /// Combined Shape (b) + Shape (a) with storage-backed keys across a re-entrant RHS call.
    function setReentrantStorageKeys(address hook, bytes4 sel, uint256 tag) external {
        require(_bumpCounter() != 0);
        buckets[curBucket].entries[_packKey(curTarget, sel)] = LinkedConfigLib.invokeLinked(hook, tag);
    }

    /// Callback entrypoint for re-entrant callees (also exercises Shape (b) with internal stateful RHS).
    function reenterMutate(bytes32 newBucket, address newTarget, uint256 newStored) external {
        require(newStored != 999, "cb-fail");
        curBucket = newBucket;
        curTarget = newTarget;
        stored = newStored;
        emit Step(700, newStored);
        buckets[newBucket].entries[bytes32(newStored)] = _bumpCounter();
    }
}
