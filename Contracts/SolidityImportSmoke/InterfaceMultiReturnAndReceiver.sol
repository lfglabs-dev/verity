// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IStatusSource {
    function getStatus() external view returns (uint256, bool);
    function getQuote(uint256 id) external view returns (uint16, bool, address);
}

interface ITarget {
    function probe(uint256 x) external view returns (uint256);
}

interface IFactory {
    function target(uint256 id) external view returns (ITarget);
}

/// Synthetic fixture covering multi-return typed interface staticcalls and
/// general receiver expressions (internal helper, chained interface staticcall,
/// mapping/state variable, conditional) hoisted into temporaries.
contract InterfaceMultiReturnAndReceiver {
    uint256 internal lastValue;
    bool internal lastOk;
    uint256 internal lastProbe;
    ITarget internal defaultTarget;
    mapping(uint256 => address) internal targetById;
    mapping(uint256 => address) internal sourceById;

    function configure(address defTarget, uint256 id, address tgt, address src) external {
        defaultTarget = ITarget(defTarget);
        targetById[id] = tgt;
        sourceById[id] = src;
    }

    function readStatusDecl(address src) external returns (uint256, bool) {
        (uint256 value, bool ok) = IStatusSource(src).getStatus();
        lastValue = value;
        lastOk = ok;
        return (value, ok);
    }

    function readStatusAssign(address src) external returns (uint256, bool) {
        (lastValue, lastOk) = IStatusSource(src).getStatus();
        return (lastValue, lastOk);
    }

    function readStatusDirect(address src) external view returns (uint256, bool) {
        return IStatusSource(src).getStatus();
    }

    function readStatusElided(address src) external view returns (uint256) {
        (uint256 value, ) = IStatusSource(src).getStatus();
        return value;
    }

    function readStatusDiscarded(address src) external view returns (uint256) {
        IStatusSource(src).getStatus();
        return 7;
    }

    function readQuote(address src, uint256 id) external view returns (uint16, bool, address) {
        return IStatusSource(src).getQuote(id);
    }

    function _getTarget(uint256 id) internal view returns (ITarget) {
        return ITarget(targetById[id]);
    }

    function _getSource(uint256 id) internal view returns (IStatusSource) {
        return IStatusSource(sourceById[id]);
    }

    function probeViaHelper(uint256 id, uint256 x) external returns (uint256) {
        uint256 r = _getTarget(id).probe(x);
        lastProbe = r;
        return r;
    }

    function probeViaFactory(address factory, uint256 id, uint256 x) external returns (uint256) {
        uint256 r = IFactory(factory).target(id).probe(x);
        lastProbe = r;
        return r;
    }

    function probeViaState(uint256 x) external view returns (uint256) {
        return defaultTarget.probe(x);
    }

    function probeViaConditional(bool useDefault, uint256 id, uint256 x)
        external
        view
        returns (uint256)
    {
        return (useDefault ? defaultTarget : _getTarget(id)).probe(x);
    }

    function statusViaHelper(uint256 id) external view returns (uint256, bool) {
        return _getSource(id).getStatus();
    }
}
