// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface ITransientTarget {
    function ping() external view returns (uint256);
}

contract TransientStateVarBase {
    bool internal transient locked;
}

contract TransientStateVarSequence is TransientStateVarBase {
    enum Mode { Off, On }

    uint256 public count;
    uint16 private transient number;
    uint8 private transient small;
    address public transient sender;
    ITransientTarget private transient target;
    uint64 private transient stamp;
    bytes32 private transient fullWord;
    int256 private transient signedWord;
    int16 private transient delta;
    bytes4 private transient tag;
    Mode private transient mode;
    function() internal transient pointer;

    modifier nonReentrant() {
        require(!locked);
        locked = true;
        _;
        locked = false;
    }

    function pair(uint16 a, uint8 b) internal pure returns (uint16, uint8) {
        return (a, b);
    }

    function bump() external nonReentrant returns (uint256) {
        count += 1;
        return count;
    }

    function earlyReturnBump(bool early) external nonReentrant returns (uint256) {
        if (early) {
            return count + 10;
        }
        count += 1;
        return count;
    }

    function failInsideGuard() external nonReentrant {
        count += 1;
        number = 77;
        require(false, "guard rollback");
    }

    function packed() external returns (uint16, uint8, address, address, uint64, bytes32, int256) {
        number += 11;
        ++number;
        small = 200;
        small--;
        sender = address(1);
        target = ITransientTarget(address(2));
        stamp = 9;
        fullWord = bytes32(uint256(0x1234));
        signedWord = -5;
        delete small;
        return (number, small, sender, address(target), stamp, fullWord, signedWord);
    }

    function assignForms(uint16 a, uint8 b) external returns (uint16 assigned, uint256 sum) {
        assigned = (number = a);
        (number, small) = pair(assigned + 1, b);
        stamp += uint64(small);
        delete fullWord;
        return (assigned, uint256(number) + small + stamp);
    }

    function readWords() external view returns (bool, uint16, uint8, address, uint64) {
        return (locked, number, small, sender, stamp);
    }

    function lockedEquals(bool expected) external view returns (bool) {
        return locked == expected;
    }

    function readSigned() external view returns (int256) { return delta; }

    function readTag() external view returns (bytes4) { return tag; }

    function readMode() external view returns (Mode) { return mode; }

    function clearPointer() external { delete pointer; }

    function rawInRoot() external returns (uint256 word) {
        number = 5;
        assembly { word := tload(0) }
    }

    function slotInRoot() external view returns (uint256 slotWord) {
        assembly { slotWord := sender.slot }
    }

    function observe(uint16 v) internal pure returns (uint256 word) {
        assembly { word := v }
    }

    function rawInHelper() external nonReentrant returns (uint256) {
        return observe(7);
    }

    function persistentWithAssembly(uint256 x) external returns (uint256 word) {
        count = x;
        uint16 y = uint16(count);
        assembly { word := y }
    }
}

contract ShadowedTransientBase {
    uint256 private shadowed;

    function touchBase() internal { shadowed = 1; }
}

contract ShadowedTransientChild is ShadowedTransientBase {
    uint256 private transient shadowed;

    function touchChild() external {
        touchBase();
        shadowed = 2;
    }
}
