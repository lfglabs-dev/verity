// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library MathSlice42 {
    error MathOverflowedMulDiv();

    enum Rounding {
        Floor,
        Ceil,
        Trunc,
        Expand
    }

    function unsignedRoundsUp(Rounding rounding) internal pure returns (bool) {
        return uint8(rounding) % 2 == 1;
    }

    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            uint256 prod0 = x * y;
            uint256 prod1;
            assembly ("memory-safe") {
                let mm := mulmod(x, y, not(0))
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            if (prod1 == 0) {
                return prod0 / denominator;
            }

            if (denominator <= prod1) {
                revert MathOverflowedMulDiv();
            }

            uint256 remainder;
            assembly ("memory-safe") {
                remainder := mulmod(x, y, denominator)
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            uint256 twos = denominator & (0 - denominator);
            assembly ("memory-safe") {
                denominator := div(denominator, twos)
                prod0 := div(prod0, twos)
                twos := add(div(sub(0, twos), twos), 1)
            }

            prod0 |= prod1 * twos;

            uint256 inverse = (3 * denominator) ^ 2;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;
            inverse *= 2 - denominator * inverse;

            result = prod0 * inverse;
            return result;
        }
    }

    function mulDiv(uint256 x, uint256 y, uint256 denominator, Rounding rounding) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (unsignedRoundsUp(rounding) && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }
}

library ArraysSlice42 {
    function unsafeMemoryAccess(uint256[] memory arr, uint256 pos) internal pure returns (uint256 res) {
        assembly ("memory-safe") {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }

    function unsafeMemoryAccess(address[] memory arr, uint256 pos) internal pure returns (address res) {
        assembly ("memory-safe") {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }
}

library TimeSlice42 {
    using TimeSlice42 for *;

    type Delay is uint112;

    function timestamp() internal view returns (uint48) {
        return uint48(block.timestamp);
    }

    function toDelay(uint32 duration) internal pure returns (Delay) {
        return Delay.wrap(duration);
    }

    function unpack(Delay self) internal pure returns (uint32 valueBefore, uint32 valueAfter, uint48 effect) {
        uint112 raw = Delay.unwrap(self);
        valueAfter = uint32(raw);
        valueBefore = uint32(raw >> 32);
        effect = uint48(raw >> 64);
        return (valueBefore, valueAfter, effect);
    }

    function pack(uint32 valueBefore, uint32 valueAfter, uint48 effect) internal pure returns (Delay) {
        return Delay.wrap((uint112(effect) << 64) | (uint112(valueBefore) << 32) | uint112(valueAfter));
    }

    function _getFullAt(Delay self, uint48 timepoint) private pure returns (uint32, uint32, uint48) {
        (uint32 valueBefore, uint32 valueAfter, uint48 effect) = self.unpack();
        return effect <= timepoint ? (valueAfter, 0, 0) : (valueBefore, valueAfter, effect);
    }

    function getFull(Delay self) internal view returns (uint32, uint32, uint48) {
        return _getFullAt(self, timestamp());
    }

    function get(Delay self) internal view returns (uint32) {
        (uint32 delay, , ) = self.getFull();
        return delay;
    }

    function withUpdate(
        Delay self,
        uint32 newValue,
        uint32 minSetback
    ) internal view returns (Delay updatedDelay, uint48 effect) {
        uint32 value = self.get();
        uint32 diff = value > newValue ? value - newValue : 0;
        uint32 setback = minSetback > diff ? minSetback : diff;
        effect = timestamp() + setback;
        return (pack(value, newValue, effect), effect);
    }
}

contract SequenceFixture {
    using ArraysSlice42 for uint256[];
    using ArraysSlice42 for address[];
    using TimeSlice42 for *;

    enum ProposalState {
        Pending,
        Active,
        Canceled,
        Defeated,
        Succeeded,
        Queued,
        Expired,
        Executed
    }

    bytes32 private constant ALL_PROPOSAL_STATES_BITMAP =
        bytes32((2 ** (uint8(type(ProposalState).max) + 1)) - 1);

    struct Role {
        uint64 admin;
        TimeSlice42.Delay grantDelay;
    }

    event GovernorDelayAndSliceRecorded(
        uint256 indexed roleId,
        address indexed proposer,
        uint256 grantDelay,
        uint256 effectTime,
        uint256 mulDivOut
    );

    mapping(uint64 roleId => Role) private _roles;
    uint256 private _accumulatedScore;
    bytes32 private _lastDigest;
    uint48 private _lastEffect;

    function _tryHexToUint(bytes1 char) private pure returns (bool, uint8) {
        uint8 c = uint8(char);
        unchecked {
            if (47 < c && c < 58) {
                return (true, c - 48);
            } else if (64 < c && c < 71) {
                return (true, c - 55);
            } else if (96 < c && c < 103) {
                return (true, c - 87);
            } else {
                return (false, 0);
            }
        }
    }

    function _isValidDescriptionForProposer(
        address proposer,
        string memory description
    ) internal view virtual returns (bool) {
        unchecked {
            uint256 length = bytes(description).length;

            if (length < 52) {
                return true;
            }

            bytes12 marker;
            assembly ("memory-safe") {
                marker := mload(add(description, sub(length, 20)))
            }

            if (marker != bytes12("#proposer=0x")) {
                return true;
            }

            uint160 recovered = 0;
            for (uint256 i = length - 40; i < length; ++i) {
                (bool isHex, uint8 value) = _tryHexToUint(bytes(description)[i]);
                if (!isHex) {
                    return true;
                }
                recovered = (recovered << 4) | value;
            }

            return recovered == uint160(proposer);
        }
    }

    function checkProposerDescription(
        address proposer,
        string memory description
    ) public view returns (bool, uint256) {
        return (_isValidDescriptionForProposer(proposer, description), uint256(ALL_PROPOSAL_STATES_BITMAP));
    }

    function decodeSelectorAndTarget(bytes calldata data) public pure returns (bytes4, address, uint64) {
        if (data.length < 0x24) {
            return (bytes4(0), address(0), 0);
        }
        bytes4 sel = bytes4(data[0:4]);
        address target = abi.decode(data[0x04:0x24], (address));
        uint64 roleId = abi.decode(data[0x04:0x24], (uint64));
        return (sel, target, roleId);
    }

    function setRoleGrantDelay(uint64 roleId, uint32 newDelay, uint32 minSetback) public returns (uint32, uint48) {
        uint48 effect;
        (_roles[roleId].grantDelay, effect) = _roles[roleId].grantDelay.withUpdate(newDelay, minSetback);
        _lastEffect = effect;
        return (_roles[roleId].grantDelay.get(), effect);
    }

    function computeMulDivPair(uint256 x, uint256 y, uint256 denominator) public pure returns (uint256, uint256) {
        return (
            MathSlice42.mulDiv(x, y, denominator),
            MathSlice42.mulDiv(x, y, denominator, MathSlice42.Rounding.Ceil)
        );
    }

    function inspectUnsafeMemoryAndTail(
        address[] memory accounts,
        uint256[] memory amounts,
        uint256 idx
    ) public view returns (address, uint256, address) {
        address tailAddr = msg.sender;
        uint256 calldataLength = msg.data.length;
        if (calldataLength >= 20) {
            tailAddr = address(bytes20(msg.data[calldataLength - 20:]));
        }
        return (accounts.unsafeMemoryAccess(idx), amounts.unsafeMemoryAccess(idx), tailAddr);
    }

    function change(uint256 input) external returns (uint256) {
        uint64 roleId = uint64((input & 0x03) + 1);
        uint32 newDelay = uint32(((input & 0x0f) + 1) * 5);
        uint48 effect;
        (_roles[roleId].grantDelay, effect) = _roles[roleId].grantDelay.withUpdate(newDelay, 7);
        _roles[roleId].admin = roleId + 10;
        _lastEffect = effect;

        address expectedProposer = 0x111122223333444455556666777788889999aAaa;
        string memory validTagged = "Proposal: upgrade vault#proposer=0x111122223333444455556666777788889999aAaa";
        string memory shortUntagged = "Short proposal";
        bool matchValid = _isValidDescriptionForProposer(expectedProposer, validTagged);
        bool mismatchOther = _isValidDescriptionForProposer(msg.sender, validTagged);
        bool allowShort = _isValidDescriptionForProposer(msg.sender, shortUntagged);
        require(matchValid && !mismatchOther && allowShort, "GSPD: proposer description check failed");

        uint256 bigX = (uint256(1) << 192) + (input + 3);
        uint256 bigY = (uint256(1) << 128) + 9;
        uint256 denom = (uint256(1) << 128) + 3;
        uint256 floorMd = MathSlice42.mulDiv(bigX, bigY, denom);
        uint256 ceilMd = MathSlice42.mulDiv(bigX, bigY, denom, MathSlice42.Rounding.Ceil);
        require(ceilMd >= floorMd && ceilMd - floorMd <= 1, "GSPD: mulDiv rounding mismatch");

        uint256 calldataLength = msg.data.length;
        address tailSender = msg.sender;
        if (calldataLength >= 20) {
            bytes20 tailBytes = bytes20(msg.data[calldataLength - 20:]);
            tailSender = address(tailBytes);
        }

        bytes12 tag12 = bytes12("#proposer=0x");
        uint96 tagWord = uint96(tag12);
        bytes20 sender20 = bytes20(expectedProposer);
        uint160 senderWord = uint160(sender20);
        require(senderWord == uint160(expectedProposer) && tagWord > 0, "GSPD: fixed bytes cast mismatch");

        uint32 activeDelay = _roles[roleId].grantDelay.get();
        emit GovernorDelayAndSliceRecorded(uint256(roleId), expectedProposer, uint256(activeDelay), uint256(effect), ceilMd & 0xffffffff);

        unchecked {
            _accumulatedScore +=
                (ceilMd & 0xffff) +
                (floorMd & 0xffff) +
                uint256(activeDelay) +
                uint256(effect & 0xffff) +
                uint256(ALL_PROPOSAL_STATES_BITMAP) +
                (uint256(uint160(tailSender)) & 0xff);
        }
        _lastDigest =
            bytes32(tag12) ^
            bytes32(sender20) ^
            bytes32(ceilMd) ^
            ALL_PROPOSAL_STATES_BITMAP;
        require(input != 20, "GSPD: rollback");
        return _accumulatedScore;
    }

    function fail() external {
        _accumulatedScore += 777;
        _lastEffect += 111;
        revert("GSPD: fail");
    }

    function read() external view returns (uint256, bytes32, uint48, uint32) {
        return (
            _accumulatedScore,
            _lastDigest,
            _lastEffect,
            _roles[1].grantDelay.get() + _roles[2].grantDelay.get()
        );
    }
}
