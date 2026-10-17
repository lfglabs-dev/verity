// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library TimeSlice43 {
    using TimeSlice43 for *;

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

abstract contract ContextSlice43 {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

contract SequenceFixture is ContextSlice43 {
    using TimeSlice43 for *;

    struct Access {
        uint48 since;
        TimeSlice43.Delay delay;
    }

    struct Role {
        mapping(address user => Access access) members;
        uint64 admin;
        uint64 guardian;
        TimeSlice43.Delay grantDelay;
    }

    struct TargetConfig {
        mapping(bytes4 selector => uint64 roleId) allowedRoles;
        TimeSlice43.Delay adminDelay;
        bool closed;
    }

    uint64 public constant ADMIN_ROLE = type(uint64).min;
    uint64 public constant PUBLIC_ROLE = type(uint64).max;

    event TargetFunctionRoleUpdated(address indexed target, bytes4 selector, uint64 indexed roleId);
    event TargetAdminConfigured(
        address indexed target,
        address indexed member,
        uint256 roleId,
        uint256 delay,
        uint256 since
    );

    mapping(address target => TargetConfig mode) private _targets;
    mapping(uint64 roleId => Role) private _roles;
    mapping(bytes4 selector => uint256 count) private _selectorExecCount;
    uint256 private _accumulatedScore;
    bytes32 private _lastDigest;
    uint64 private _lastRoleId;

    function getTargetFunctionRole(address target, bytes4 selector) public view virtual returns (uint64) {
        return _targets[target].allowedRoles[selector];
    }

    function isTargetClosed(address target) public view virtual returns (bool) {
        return _targets[target].closed;
    }

    function getTargetAdminDelay(address target) public view virtual returns (uint32) {
        return _targets[target].adminDelay.get();
    }

    function getRoleAdmin(uint64 roleId) public view virtual returns (uint64) {
        return _roles[roleId].admin;
    }

    function getRoleGuardian(uint64 roleId) public view virtual returns (uint64) {
        return _roles[roleId].guardian;
    }

    function getAccess(
        uint64 roleId,
        address account
    ) public view virtual returns (uint48 since, uint32 currentDelay, uint32 pendingDelay, uint48 effect) {
        Access storage access = _roles[roleId].members[account];
        since = access.since;
        (currentDelay, pendingDelay, effect) = access.delay.getFull();
        return (since, currentDelay, pendingDelay, effect);
    }

    function hasRole(
        uint64 roleId,
        address account
    ) public view virtual returns (bool isMember, uint32 executionDelay) {
        if (roleId == PUBLIC_ROLE) {
            return (true, 0);
        } else {
            (uint48 hasRoleSince, uint32 currentDelay, , ) = getAccess(roleId, account);
            return (hasRoleSince != 0 && hasRoleSince <= TimeSlice43.timestamp(), currentDelay);
        }
    }

    function canCall(
        address callerAddr,
        address target,
        bytes4 selector
    ) public view virtual returns (bool immediate, uint32 delay) {
        if (isTargetClosed(target)) {
            return (false, 0);
        } else if (callerAddr == address(this)) {
            return (true, 0);
        } else {
            uint64 roleId = getTargetFunctionRole(target, selector);
            (bool isMember, uint32 currentDelay) = hasRole(roleId, callerAddr);
            return isMember ? (currentDelay == 0, currentDelay) : (false, 0);
        }
    }

    function _checkSelector(bytes calldata data) private pure returns (bytes4) {
        return bytes4(data[0:4]);
    }

    function _getAdminRestrictions(
        bytes calldata data
    ) private view returns (bool restricted, uint64 roleAdminId, uint32 executionDelay) {
        if (data.length < 4) {
            return (false, 0, 0);
        }

        bytes4 selector = _checkSelector(data);

        if (
            selector == this.setTargetFunctionRole.selector ||
            selector == this.configureMemberAndTarget.selector
        ) {
            if (data.length < 0x24) {
                return (false, 0, 0);
            }
            address target = abi.decode(data[0x04:0x24], (address));
            uint32 delay = getTargetAdminDelay(target);
            return (true, ADMIN_ROLE, delay);
        }

        if (selector == this.checkCallPermission.selector) {
            if (data.length < 0x44) {
                return (false, 0, 0);
            }
            uint64 roleId = abi.decode(data[0x24:0x44], (uint64));
            return (true, getRoleAdmin(roleId), 0);
        }

        return (false, getTargetFunctionRole(address(this), selector), 0);
    }

    function _canCallExtended(
        address caller,
        bytes calldata data
    ) private view returns (bool immediate, uint32 delay) {
        (bool enabled, uint64 roleId, uint32 operationDelay) = _getAdminRestrictions(data);
        if (!enabled) {
            return (false, 0);
        }

        (bool inRole, uint32 executionDelay) = hasRole(roleId, caller);
        if (!inRole) {
            return (false, 0);
        }

        delay = operationDelay > executionDelay ? operationDelay : executionDelay;
        return (delay == 0, delay);
    }

    function _canCallSelf(address caller, bytes calldata data) private view returns (bool immediate, uint32 delay) {
        if (data.length < 4) {
            return (false, 0);
        }

        if (caller == address(this)) {
            return (true, 0);
        }

        if (isTargetClosed(address(this))) {
            return (false, 0);
        }

        (bool enabled, uint32 currentDelay) = canCall(caller, address(this), _checkSelector(data));
        if (!enabled) {
            return _canCallExtended(caller, data);
        }
        return (enabled, currentDelay);
    }

    function checkCallPermission(
        address callerAddr,
        address target,
        bytes calldata data
    ) public view returns (bool immediate, uint32 delay) {
        if (target == address(this)) {
            return _canCallSelf(callerAddr, data);
        } else {
            return data.length < 4 ? (false, 0) : canCall(callerAddr, target, _checkSelector(data));
        }
    }

    function _storeTargetFunctionRole(address target, bytes4 selector, uint64 roleId) internal virtual {
        _targets[target].allowedRoles[selector] = roleId;
        _selectorExecCount[selector] += 1;
    }

    function _setTargetFunctionRole(address target, bytes4 selector, uint64 roleId) internal virtual {
        _storeTargetFunctionRole(target, selector, roleId);
        emit TargetFunctionRoleUpdated(target, selector, roleId);
    }

    function setSingleTargetFunctionRole(address target, bytes4 selector, uint64 roleId) public virtual {
        _setTargetFunctionRole(target, selector, roleId);
        _lastRoleId = roleId;
    }

    function _hashSelectors(bytes4[] memory selectors) private pure returns (bytes32 acc) {
        acc = bytes32(selectors.length);
        for (uint256 i = 0; i < selectors.length; ++i) {
            bytes4 sel = selectors[i];
            acc = keccak256(abi.encodePacked(acc, sel));
        }
    }

    function setTargetFunctionRole(
        address target,
        bytes4[] calldata selectors,
        uint64 roleId
    ) public virtual returns (uint256 count, bytes32 digest) {
        count = selectors.length;
        for (uint256 i = 0; i < count; ++i) {
            _storeTargetFunctionRole(target, selectors[i], roleId);
        }
        digest = _hashSelectors(selectors);
        _lastDigest = digest;
        _lastRoleId = roleId;
    }

    function decodeSelectorsAndRole(bytes calldata payload) public pure returns (bytes4 firstSel, uint256 count) {
        bytes4[] memory decoded = abi.decode(payload, (bytes4[]));
        count = decoded.length;
        firstSel = count > 0 ? decoded[0] : bytes4(0);
    }

    function configureMemberAndTarget(
        address target,
        address member,
        uint64 roleId,
        uint32 memberDelay,
        uint32 targetAdminDelay,
        bool closed
    ) public returns (uint48 effect) {
        _roles[roleId].admin = roleId + 1;
        _roles[roleId].guardian = roleId + 2;
        _roles[roleId].members[member] = Access({
            since: TimeSlice43.timestamp(),
            delay: memberDelay.toDelay()
        });
        _targets[target].closed = closed;
        (_targets[target].adminDelay, effect) = _targets[target].adminDelay.withUpdate(targetAdminDelay, 0);
        emit TargetAdminConfigured(target, member, uint256(roleId), uint256(targetAdminDelay), uint256(effect));
    }

    function tryHexToUint(bytes1 char) public pure returns (bool, uint8) {
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

    function parseHexByte(
        bytes1 c,
        bytes calldata raw
    ) public pure returns (bool isHex, uint8 nib, bytes1 decodedByte, bytes32 digest) {
        (isHex, nib) = tryHexToUint(c);
        decodedByte = raw.length >= 32 ? abi.decode(raw, (bytes1)) : bytes1("0");
        digest = keccak256(bytes.concat(c, decodedByte, bytes1(0x3a))) ^ keccak256(abi.encodePacked(c, decodedByte));
    }

    function _hashCalldataSlice(bytes calldata sliceData) private pure returns (bytes32) {
        return keccak256(sliceData);
    }

    function _inspectMsgData(bytes calldata data) private pure returns (bytes4 sel, uint256 argWord, bytes32 tailHash) {
        sel = _checkSelector(data);
        argWord = abi.decode(data[0x04:0x24], (uint256));
        tailHash = _hashCalldataSlice(data) ^ keccak256(data[0x04:0x24]);
    }

    function change(uint256 input) external returns (uint256) {
        address target = address(uint160(0xdead0000 + (input & 0x03)));
        address caller = address(uint160(0xbeef0000 + (input & 0x03)));
        bytes4 sel = bytes4(uint32(0x11223340 + (input & 0x07)));
        uint64 roleId = uint64((input & 0x07) + 1);
        uint32 memberDelay = uint32((input & 0x03) * 10);
        uint32 adminDelay = uint32(((input >> 1) & 0x03) * 5);

        uint48 effect = configureMemberAndTarget(target, caller, roleId, memberDelay, adminDelay, false);
        _storeTargetFunctionRole(target, sel, roleId);

        uint64 assignedRole = getTargetFunctionRole(target, sel);
        require(assignedRole == roleId, "AMTR: target role mismatch");

        (bool imm, uint32 callDelay) = canCall(caller, target, sel);
        require(imm == (memberDelay == 0) && callDelay == memberDelay, "AMTR: canCall mismatch");

        (bytes4 msgSel, uint256 msgArg, bytes32 sliceDigest) = _inspectMsgData(_msgData());
        require(msgSel == this.change.selector && msgArg == input, "AMTR: calldata helper slice mismatch");

        (bool selfRestricted, uint64 selfAdminRole, ) = _getAdminRestrictions(_msgData());
        require(!selfRestricted && selfAdminRole == getTargetFunctionRole(address(this), msgSel), "AMTR: admin restriction mismatch");

        bytes1 hexChar = (input & 1 == 0) ? bytes1("a") : bytes1("9");
        (bool okHex, uint8 nib) = tryHexToUint(hexChar);
        require(okHex && nib == ((input & 1 == 0) ? 10 : 9), "AMTR: hex byte mismatch");

        bytes32 byteDigest = keccak256(bytes.concat(hexChar, bytes1(0x3a))) ^ keccak256(abi.encodePacked(hexChar, sel));
        _lastDigest = sliceDigest ^ byteDigest;
        _lastRoleId = assignedRole;

        unchecked {
            _accumulatedScore +=
                uint256(assignedRole) +
                uint256(callDelay) +
                uint256(effect & 0xffff) +
                uint256(nib) +
                _selectorExecCount[sel] +
                (uint256(_lastDigest) & 0xffff);
        }
        require(input != 20, "AMTR: rollback");
        return _accumulatedScore;
    }

    function fail() external {
        _accumulatedScore += 888;
        _lastRoleId += 77;
        revert("AMTR: fail");
    }

    function read() external view returns (uint256, bytes32, uint64, uint256) {
        bytes4 sel0 = bytes4(uint32(0x11223340));
        bytes4 sel1 = bytes4(uint32(0x11223341));
        return (
            _accumulatedScore,
            _lastDigest,
            _lastRoleId,
            _selectorExecCount[sel0] + _selectorExecCount[sel1]
        );
    }
}
