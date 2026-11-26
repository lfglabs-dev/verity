// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Modifiers on entry points and internal helpers in a forwarded `(bool, bytes memory)`
// tuple call tree (#2803): chained pre/post side effects, caller-context setup/reset
// read by forwarded-call arguments and helpers, reverting modifiers (pre and post on
// root and helper), EIP-1153 transient reentrancy guards (`transient bool` and Yul
// `tload`/`tstore`), substituted branch/repeated `_;` modifiers (#2846), and empty,
// short and multi-word `bytes` payloads.
contract SequenceFixture {
    error GuardLocked();
    error UnauthorizedCaller(address caller);
    error StepRejected(uint256 step);

    bytes32 private constant _ASM_LOCK_SLOT =
        0x778899aabbccddeeff00112233445566778899aabbccddeeff00112233445566;

    uint256 private trace;
    address private activeCaller;
    mapping(address => bytes32) private callerTag;
    bool private transient transientLock;

    modifier nonReentrant() {
        if (transientLock) {
            revert GuardLocked();
        }
        transientLock = true;
        trace = (trace % (1 << 200)) * 16 + 1;
        _;
        trace = (trace % (1 << 200)) * 16 + 14;
        transientLock = false;
    }

    modifier callerContext(uint256 gateCode) {
        if (activeCaller != address(0)) {
            revert GuardLocked();
        }
        if (gateCode == 11) {
            revert UnauthorizedCaller(msg.sender);
        }
        activeCaller = msg.sender;
        callerTag[msg.sender] = bytes32(uint256(0x9000 + (gateCode % 32)));
        trace = (trace % (1 << 200)) * 16 + 2;
        _;
        bytes memory scratch = abi.encode(uint256(0xdeadbeef), trace, msg.sender);
        if (scratch.length == 0) {
            revert();
        }
        if (gateCode == 12) {
            revert StepRejected(gateCode);
        }
        activeCaller = address(0);
        trace = (trace % (1 << 200)) * 16 + 13;
    }

    modifier nonReentrantAsm() {
        assembly ("memory-safe") {
            if tload(_ASM_LOCK_SLOT) { revert(0, 0) }
            tstore(_ASM_LOCK_SLOT, 1)
        }
        trace = (trace % (1 << 200)) * 16 + 1;
        _;
        trace = (trace % (1 << 200)) * 16 + 14;
        assembly ("memory-safe") {
            tstore(_ASM_LOCK_SLOT, 0)
        }
    }

    modifier helperGuard(uint256 step) {
        if (step == 13) {
            revert StepRejected(step);
        }
        trace = (trace % (1 << 200)) * 16 + 3;
        _;
        if (step == 14) {
            revert StepRejected(step);
        }
        trace = (trace % (1 << 200)) * 16 + 12;
    }

    modifier nestedAudit() {
        trace = (trace % (1 << 200)) * 16 + 4;
        _;
        trace = (trace % (1 << 200)) * 16 + 11;
    }

    modifier twice() {
        trace = (trace % (1 << 200)) * 16 + 5;
        _;
        trace = (trace % (1 << 200)) * 16 + 5;
        _;
        trace = (trace % (1 << 200)) * 16 + 7;
    }

    modifier maybeRun(uint256 selector) {
        if (selector % 3 != 0) {
            _;
        } else {
            trace = (trace % (1 << 200)) * 16 + 8;
        }
    }

    function _currentActor() internal view returns (address) {
        return activeCaller;
    }

    function _readContextTag(bytes32 roleTag) private nestedAudit returns (uint256 digest) {
        require(activeCaller != address(0), "missing caller context");
        digest = (uint256(roleTag) & 0xffff) + (uint256(uint160(activeCaller)) % 97);
    }

    function _executeReturnData(
        address actor,
        bytes32 roleTag,
        uint256 mode,
        uint256 payloadSeed
    ) private helperGuard(mode) returns (bool success, bytes memory returnData) {
        uint256 tagDigest = _readContextTag(roleTag);
        require(mode != 15, "helper body revert");
        trace = (trace % (1 << 200)) * 16 + 9;
        uint256 shape = mode % 5;
        if (shape == 0) {
            success = false;
        } else if (shape == 1) {
            success = true;
            returnData = abi.encodePacked();
        } else if (shape == 2) {
            success = (actor == msg.sender);
            returnData = abi.encodePacked(uint32(payloadSeed), uint8(tagDigest));
        } else if (shape == 3) {
            success = true;
            returnData = abi.encode(trace ^ tagDigest ^ payloadSeed);
        } else {
            success = (actor == msg.sender);
            returnData = abi.encodePacked(
                trace,
                bytes32(payloadSeed ^ 0x1122334455667788),
                uint24(tagDigest + 0xabcdef)
            );
        }
    }

    function _executePlain(
        uint256 mode,
        uint256 payloadSeed
    ) private helperGuard(mode) returns (bool success, bytes memory returnData) {
        require(mode != 15, "plain helper revert");
        trace = (trace % (1 << 200)) * 16 + 10;
        uint256 shape = mode % 4;
        if (shape == 0) {
            success = false;
        } else if (shape == 1) {
            success = true;
            returnData = abi.encodePacked(uint16(payloadSeed + 1), uint8(trace));
        } else if (shape == 2) {
            success = true;
            returnData = abi.encode(trace, payloadSeed);
        } else {
            success = true;
            returnData = abi.encodePacked(
                trace,
                bytes32(payloadSeed ^ 0xaabbccddeeff0011),
                bytes32(trace ^ 0x5566778899aabbcc),
                uint16(0xcafe)
            );
        }
    }

    function change(uint256 x)
        external
        nonReentrant
        callerContext(x % 16)
        returns (bool success, bytes memory returnData)
    {
        return _executeReturnData(
            _currentActor(),
            callerTag[_currentActor()],
            x % 16,
            x >> 4
        );
    }

    function execAsmGuard(uint256 x) external nonReentrantAsm returns (bool, bytes memory) {
        return _executePlain(x % 16, x >> 4);
    }

    function execSubstituted(uint256 x)
        external
        twice
        maybeRun(trace + x)
        returns (bool success, bytes memory returnData)
    {
        success = true;
        returnData = abi.encodePacked(uint16(0xdead));
        return _executePlain(x % 16, x >> 4);
    }

    function execBranch(uint256 x)
        external
        nonReentrant
        callerContext(x % 8)
        returns (bool success, bytes memory returnData)
    {
        if (x % 2 == 0) {
            return _executeReturnData(
                _currentActor(),
                callerTag[_currentActor()],
                x % 5,
                x >> 4
            );
        }
        success = (activeCaller == msg.sender);
        returnData = abi.encodePacked(uint16(x), uint64(trace));
    }

    function fail() external nonReentrant {
        trace = (trace % (1 << 200)) * 16 + 15;
        revert GuardLocked();
    }

    function read() external view returns (uint256) {
        return (trace << 1) ^ (activeCaller == address(0) ? 0 : 1);
    }
}
