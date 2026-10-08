// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant ZERO_WORD = 0;
uint256 constant CBP_SCALE = 1e6;
uint256 constant LOCK_BASE_SLOT = uint256(keccak256("verity.smoke.transient.lock"));

contract SequenceFixture {
    error InvalidApprover(address approver);
    error InvalidSpender(address spender);
    error BoundError(address zeroAddr, uint8 maxByte, uint256 zeroConst);

    event ApprovalRecorded(address indexed owner, address indexed spender, uint256 value);

    uint256 private savedStart;
    uint256 private savedEnd;
    uint256 private feeAccumulator;
    uint256 private approvalCount;
    mapping(address => mapping(address => uint256)) private allowances;
    mapping(uint256 => uint16) private feeCbp;

    function _tGet(uint256 baseSlot, bytes32 key1, address key2) internal view returns (bool value) {
        uint256 slot = uint256(keccak256(abi.encode(key1, key2, baseSlot)));
        assembly ("memory-safe") {
            value := tload(slot)
        }
    }

    function _approve(address owner, address spender, uint256 value) internal {
        _approve(owner, spender, value, true);
    }

    function _approve(address owner, address spender, uint256 value, bool emitEvent) internal {
        if (owner == address(0)) {
            revert InvalidApprover(address(0));
        }
        if (spender == address(0)) {
            revert InvalidSpender(address(0));
        }
        allowances[owner][spender] = value;
        if (emitEvent) {
            approvalCount += 1;
            emit ApprovalRecorded(owner, spender, value);
        }
    }

    function change(uint256 input) external returns (uint256) {
        require(input != 19, BoundError(address(0), type(uint8).max, ZERO_WORD));
        uint256 seed = input % 500000;
        address owner = seed == 96 ? address(0) : msg.sender;
        address spender = seed == 97 ? address(0) : address(this);

        if ((seed % 2) == 0) {
            _approve(owner, spender, seed + 10);
        } else {
            _approve(owner, spender, seed + 20, false);
        }

        feeCbp[0] = uint16((seed % 50) + 1);
        feeCbp[1] = uint16((seed % 70) + 2);
        feeCbp[2] = uint16((seed % 90) + 3);

        uint256 maturity = (seed % 10) * 1 days;
        (uint256 start, uint256 end, uint256 feeLower, uint256 feeUpper) =
            maturity < 1 days ? (0 days, 1 days, feeCbp[0] * CBP_SCALE, feeCbp[1] * CBP_SCALE) :
            maturity < 7 days ? (1 days, 7 days, feeCbp[1] * CBP_SCALE, feeCbp[2] * CBP_SCALE) :
                                (7 days, 30 days, feeCbp[2] * CBP_SCALE, (feeCbp[2] + 5) * CBP_SCALE);

        (savedStart, savedEnd) =
            (seed % 3 == 0) ? (start + 1, end + 2) : (start + 3, end + 4);

        bool locked = _tGet(LOCK_BASE_SLOT, bytes32(seed), msg.sender);
        uint256 interpolated = (feeLower * (end - maturity) + feeUpper * (maturity - start)) / (end - start);
        feeAccumulator += interpolated + (locked ? 1000 : 1) + allowances[owner][spender];

        require(input != 20, "overload const error cond tuple tload rollback");
        return feeAccumulator + savedStart + savedEnd + approvalCount;
    }

    function fail() external {
        feeAccumulator += 777;
        revert BoundError(address(0), type(uint8).max, ZERO_WORD);
    }

    function read() external view returns (uint256) {
        bool locked = _tGet(LOCK_BASE_SLOT, bytes32(uint256(0)), msg.sender);
        return savedStart + savedEnd + feeAccumulator + approvalCount
            + allowances[msg.sender][address(this)]
            + feeCbp[0] + feeCbp[1] + feeCbp[2]
            + (locked ? 1 : 0);
    }
}
