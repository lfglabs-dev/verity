// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IERC165Lite {
    function supportsInterface(bytes4 interfaceId) external view returns (bool);
}

interface IAccessControlLite {
    function hasRole(bytes32 role, address account) external view returns (bool);
    function getRoleAdmin(bytes32 role) external view returns (bytes32);
    function grantRole(bytes32 role, address account) external;
    function revokeRole(bytes32 role, address account) external;
}

contract SequenceFixture {
    struct RoleData {
        mapping(address => bool) hasRole;
        mapping(bytes32 => uint256) weights;
        mapping(address => uint128) caps;
        bytes32 adminRole;
        uint64 grantCount;
    }

    bytes32 public constant DEFAULT_ADMIN_ROLE = 0x00;
    bytes32 public constant OPERATOR_ROLE = keccak256("OPERATOR_ROLE");
    bytes4 public constant CUSTOM_IFACE = 0x12345678;

    error AccessControlUnauthorizedAccount(address account, bytes32 neededRole);
    error AccessControlBadConfirmation();

    event RoleAdminChanged(
        bytes32 indexed role,
        bytes32 indexed previousAdminRole,
        bytes32 indexed newAdminRole
    );
    event RoleGranted(
        bytes32 indexed role,
        address indexed account,
        address indexed sender
    );
    event RoleRevoked(
        bytes32 indexed role,
        address indexed account,
        address indexed sender
    );
    event RoleStepRecorded(
        uint256 indexed totalScore,
        bytes32 indexed lastDigest,
        uint256 roleWeight,
        uint256 grantCount
    );

    mapping(bytes32 => RoleData) private _roles;
    mapping(uint256 => mapping(bytes32 => RoleData)) private _scopedRoles;
    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private lastRoleWeight;
    uint64 private lastGrantCount;

    function _msgSender() internal view returns (address) {
        return msg.sender;
    }

    function supportsInterface(bytes4 interfaceId) public view returns (bool) {
        return
            interfaceId == type(IAccessControlLite).interfaceId ||
            interfaceId == type(IERC165Lite).interfaceId ||
            interfaceId == CUSTOM_IFACE;
    }

    function hasRole(bytes32 role, address account) public view returns (bool) {
        return _roles[role].hasRole[account];
    }

    function getRoleAdmin(bytes32 role) public view returns (bytes32) {
        return _roles[role].adminRole;
    }

    function _checkRole(bytes32 role, address account) internal view {
        if (!hasRole(role, account)) {
            revert AccessControlUnauthorizedAccount(account, role);
        }
    }

    function _setRoleAdmin(bytes32 role, bytes32 adminRole) internal {
        bytes32 previousAdminRole = getRoleAdmin(role);
        _roles[role].adminRole = adminRole;
        emit RoleAdminChanged(role, previousAdminRole, adminRole);
    }

    function _grantRole(bytes32 role, address account) internal returns (bool) {
        if (!hasRole(role, account)) {
            _roles[role].hasRole[account] = true;
            _roles[role].grantCount += 1;
            emit RoleGranted(role, account, _msgSender());
            return true;
        } else {
            return false;
        }
    }

    function _revokeRole(bytes32 role, address account) internal returns (bool) {
        if (hasRole(role, account)) {
            _roles[role].hasRole[account] = false;
            emit RoleRevoked(role, account, _msgSender());
            return true;
        } else {
            return false;
        }
    }

    function _scrubSelector(bytes4 sel, uint32 maskVal) internal pure returns (bytes4 out) {
        bytes4 maskBytes = bytes4(maskVal);
        bytes4 combined = (sel ^ maskBytes) | CUSTOM_IFACE;
        combined &= ~bytes4(uint32(0x0000000f));
        combined ^= type(IERC165Lite).interfaceId;
        if (combined < CUSTOM_IFACE) {
            out = combined | bytes4(bytes32(uint256(0xaa000000) << 224));
        } else {
            out = combined;
        }
    }

    function _syncScopedRole(
        uint256 scopeId,
        bytes32 role,
        address account,
        bytes32 weightTag,
        uint256 delta
    ) internal returns (uint256) {
        RoleData storage scoped = _scopedRoles[scopeId][role];
        scoped.hasRole[account] = (delta & 1) == 0;
        scoped.weights[weightTag] += delta + 3;
        uint256 w = ++scoped.weights[weightTag];
        scoped.caps[account] = uint128(delta & 0xffffffff);
        scoped.grantCount += 1;
        if ((delta & 3) == 2) {
            delete scoped.hasRole[account];
            delete scoped.caps[account];
        }
        uint256 activeBit = scoped.hasRole[account] ? 1 : 0;
        return w + uint256(scoped.caps[account]) + uint256(scoped.grantCount) + activeBit;
    }

    function checkInterface(bytes4 interfaceId, uint256 tag) external returns (bool, bytes4, uint32) {
        bool ok = supportsInterface(interfaceId);
        bytes4 scrubbed = _scrubSelector(interfaceId, uint32(tag & 0xffffffff));
        uint32 word32 = uint32(scrubbed);
        bytes32 digest = keccak256(
            abi.encodePacked(
                interfaceId,
                scrubbed,
                bytes.concat(interfaceId, type(IAccessControlLite).interfaceId),
                abi.encode(interfaceId, scrubbed, tag)
            )
        );
        lastDigest = digest;
        uint256 bonus = ok ? 100 : 10;
        totalScore += (uint256(digest) & 0xffff) + uint256(word32 & 0xff) + bonus;
        emit RoleStepRecorded(totalScore, lastDigest, lastRoleWeight, uint256(lastGrantCount));
        return (ok, scrubbed, word32);
    }

    function change(uint256 input) external returns (uint256) {
        bytes32 role = (input & 1) == 0 ? OPERATOR_ROLE : DEFAULT_ADMIN_ROLE;
        address caller = _msgSender();
        address peer = address(uint160(0x4000 + (input & 7)));

        if (input == 21) {
            _checkRole(OPERATOR_ROLE, peer);
        }

        uint256 branch = input % 3;
        if (branch == 0) {
            _setRoleAdmin(OPERATOR_ROLE, DEFAULT_ADMIN_ROLE);
            _grantRole(role, caller);
        } else if (branch == 1) {
            _revokeRole(role, peer);
        } else {
            delete _roles[role].hasRole[peer];
            delete _roles[role].weights[bytes32(input)];
        }

        bytes32 weightKey = bytes32((input & 3) + 1);
        _roles[role].weights[weightKey] += (input & 0xff) + 5;
        uint256 weightNow = _roles[role].weights[weightKey]++;
        _roles[role].caps[caller] += uint128((input & 0x7f) + 1);

        uint256 scopedMetric = _syncScopedRole(
            input & 1,
            role,
            caller,
            weightKey,
            (input & 0xff) + 1
        );

        bytes4 probeIface = (input & 2) == 0
            ? type(IAccessControlLite).interfaceId
            : ((input & 4) == 0 ? type(IERC165Lite).interfaceId : bytes4(uint32(input)));
        bool ifaceSupported = supportsInterface(probeIface);
        bytes4 scrubbed = _scrubSelector(probeIface, uint32(input));
        uint32 scrubbedWord = uint32(scrubbed);

        bytes32 digest = keccak256(
            abi.encodePacked(
                role,
                weightNow,
                scopedMetric,
                probeIface,
                scrubbed,
                bytes32(scrubbed),
                ifaceSupported
            )
        );

        lastDigest = digest;
        lastRoleWeight = _roles[role].weights[weightKey] + scopedMetric + uint256(_roles[role].caps[caller]);
        lastGrantCount = _roles[role].grantCount;
        uint256 delta = (uint256(digest) & 0xffffffff) + lastRoleWeight + uint256(scrubbedWord & 0xffff);
        totalScore += delta;

        emit RoleStepRecorded(totalScore, lastDigest, lastRoleWeight, uint256(lastGrantCount));
        require(input != 20, "struct mapping bytes4 rollback");
        return totalScore;
    }

    function fail() external {
        _roles[OPERATOR_ROLE].hasRole[_msgSender()] = true;
        _roles[OPERATOR_ROLE].weights[OPERATOR_ROLE] += 777;
        totalScore += 999;
        if (_msgSender() != address(0)) {
            revert AccessControlBadConfirmation();
        }
    }

    function read() external view returns (uint256, bytes32, uint256, uint64) {
        uint256 roleBit = hasRole(OPERATOR_ROLE, _msgSender()) ? 1 : 0;
        return (totalScore + roleBit, lastDigest, lastRoleWeight, lastGrantCount);
    }
}
