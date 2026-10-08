// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library MathEnumLib {
    enum Rounding {
        Floor,
        Ceil,
        Trunc,
        Expand
    }

    function stepRounding(Rounding r, uint256 x) internal pure returns (Rounding next, uint256 adjusted) {
        if (r == Rounding.Floor) {
            next = type(Rounding).min;
            adjusted = x + uint256(uint8(r));
        } else if (r == Rounding.Expand) {
            next = type(Rounding).max;
            adjusted = x + uint256(uint8(type(Rounding).max)) * 10;
        } else {
            next = Rounding(uint8(r) - 1);
            adjusted = x + uint256(r) * 3;
        }
    }
}

abstract contract ContextBase {
    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

contract SequenceFixture is ContextBase {
    enum Mode {
        Disabled,
        Standard,
        Turbo
    }

    error BadMode(Mode mode, uint8 maxOrd);
    event ModeApplied(Mode indexed mode, uint256 nextOrd, uint256 msgBytes);

    uint256 private totalScore;
    uint8 private lastModeOrd;
    uint256 private lastCalldataLen;

    function _selectMode(uint256 raw) internal pure returns (Mode) {
        return Mode(raw);
    }

    function echoMsgData() external view returns (bytes memory) {
        return _msgData();
    }

    function applyRounding(Mode mode, uint256 value) external returns (Mode, uint256) {
        MathEnumLib.Rounding r = mode == Mode.Turbo
            ? MathEnumLib.Rounding.Expand
            : MathEnumLib.Rounding(uint8(mode));
        (MathEnumLib.Rounding nextR, uint256 adj) = MathEnumLib.stepRounding(r, value);
        uint256 msgLen = _msgData().length + msg.data.length;
        totalScore += adj + uint256(uint8(nextR)) + msgLen;
        lastModeOrd = uint8(mode);
        lastCalldataLen = _msgData().length;
        emit ModeApplied(mode, uint256(uint8(nextR)), _msgData().length);
        return (mode, totalScore);
    }

    function change(uint256 input) external returns (uint256) {
        uint256 rawMode = (input == 19) ? 3 : (input % 3);
        Mode m = _selectMode(rawMode);
        if (input == 21) {
            revert BadMode(m, uint8(type(Mode).max));
        }
        MathEnumLib.Rounding r = (m == type(Mode).max)
            ? MathEnumLib.Rounding.Expand
            : MathEnumLib.Rounding(uint8(m));
        (MathEnumLib.Rounding nextR, uint256 adj) = MathEnumLib.stepRounding(r, input % 1000);
        uint256 span = _msgData().length + msg.data.length;
        totalScore += adj + uint256(uint8(nextR)) + span;
        lastModeOrd = uint8(m);
        lastCalldataLen = _msgData().length;
        emit ModeApplied(Mode.Standard, uint256(uint8(nextR)), msg.data.length);
        require(input != 20, "enum msgdata rollback");
        return totalScore;
    }

    function fail() external {
        totalScore += 999;
        lastModeOrd = uint8(Mode.Turbo);
        revert BadMode(Mode.Turbo, uint8(type(Mode).max));
    }

    function read() external view returns (uint256, uint8, uint256, Mode) {
        Mode current = lastModeOrd <= uint8(type(Mode).max) ? Mode(lastModeOrd) : Mode.Disabled;
        return (totalScore, lastModeOrd, lastCalldataLen + msg.data.length, current);
    }
}
