// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IPriceOracle {
    function price() external view returns (uint256);
}

contract InterfaceStaticCallFixture {
    uint256 private saved;
    uint256 private observed;

    function read(address oracle) external view returns (uint256) {
        uint256 value = IPriceOracle(oracle).price();
        return value;
    }

    function record(address oracle, uint256 next) external returns (uint256) {
        saved = next;
        uint256 value = IPriceOracle(oracle).price();
        observed = value;
        return value;
    }

    function ping(address oracle, uint256 reject) external returns (uint256) {
        uint256 value;
        saved = reject;
        value = IPriceOracle(oracle).price();
        IPriceOracle(oracle).price();
        if (reject % 2 != 0) revert();
        return value;
    }

    function probe(address oracle, uint256 next) external returns (uint256) {
        saved = next;
        IPriceOracle(oracle).price();
        return next;
    }

    function sum(address first, address second) external view returns (uint256) {
        return quote(first) + quote(second);
    }

    function quote(address oracle) internal view returns (uint256) {
        uint256 value = IPriceOracle(oracle).price();
        return value;
    }

    function stored() external view returns (uint256, uint256) {
        return (saved, observed);
    }
}

struct EnvelopeRecord {
    address target;
    uint256 amount;
    bytes payload;
    uint256 nonce;
}

interface IRiskGate {
    function canProceed(
        uint256 positionId,
        uint256 debtAmount,
        uint256 collateralAmount,
        uint256 unitPrice
    ) external view returns (bool);
}

interface IComplianceGate {
    function isPermitted(
        uint256 positionId,
        uint256 nextLimit,
        address caller
    ) external view returns (bool);
}

interface IApprovalPool {
    function onApproveEnvelope(
        address coordinator,
        address proposer,
        EnvelopeRecord calldata record,
        bytes calldata signature
    ) external view returns (bytes32);

    function hasApproved(bytes32 digest) external view returns (bool);
}

contract InterfaceStaticCallGateFixture {
    bytes32 public constant APPROVAL_MAGIC =
        keccak256("InterfaceStaticCallGateFixture.onApproveEnvelope");

    address public admin;
    address public complianceGate;
    mapping(bytes32 => bool) public recorded;

    function checkRiskGate(
        address gateTarget,
        uint256 positionId,
        uint256 debtAmount,
        uint256 collateralAmount,
        uint256 unitPrice
    ) external view returns (uint256) {
        require(
            IRiskGate(gateTarget).canProceed(
                positionId,
                debtAmount,
                collateralAmount,
                unitPrice
            ),
            "Risk gate rejected"
        );
        return debtAmount + collateralAmount;
    }

    function checkComplianceOrAdmin(
        uint256 positionId,
        uint256 nextLimit,
        address account
    ) external view returns (uint256) {
        require(
            msg.sender == admin ||
                IComplianceGate(complianceGate).isPermitted(
                    positionId,
                    nextLimit,
                    account
                ),
            "Not permitted"
        );
        return nextLimit;
    }

    function approveEnvelope(
        EnvelopeRecord memory record,
        bytes memory signature
    ) external returns (bytes32) {
        require(
            IApprovalPool(record.target).onApproveEnvelope(
                address(this),
                msg.sender,
                record,
                signature
            ) == APPROVAL_MAGIC,
            "Approval failed"
        );
        bytes32 digest = keccak256(abi.encode(record));
        bool ok = IApprovalPool(record.target).hasApproved(digest);
        recorded[digest] = ok;
        return digest;
    }
}
