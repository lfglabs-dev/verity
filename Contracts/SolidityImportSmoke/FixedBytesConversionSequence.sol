// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    bytes32 private code;
    bytes32 private acc;

    error Code(bytes32 code);

    function _widen(bytes32 v) internal pure returns (bytes32) {
        return v;
    }

    function _code(bytes5 c) internal pure returns (bytes32) {
        return c;
    }

    function _pick(uint256 x) internal pure returns (bytes8) {
        if (x % 2 == 0) {
            return "GS0";
        }
        return "GS01";
    }

    function change(uint256 x) external returns (bytes32) {
        bytes4 sel = bytes4(uint32(x));
        bytes8 wide = sel;
        bytes32 word = wide;
        bytes5 c = "GS001";
        if (x % 3 == 1) {
            c = "GS013";
        }
        code = c;
        if (x % 5 == 4) {
            code = "GS025";
        }
        bool known = c == "GS001";
        bool sameSel = sel == wide;
        bytes32 flags = bytes32(uint256(known ? 1 : 0) + (sameSel ? 2 : 0));
        acc = _widen(sel) ^ word ^ _code("GS010") ^ _pick(x) ^ flags;
        if (x % 7 == 6) {
            bytes32 widened = c;
            revert Code(widened);
        }
        return acc;
    }

    function fail() external {
        bytes32 failed = "FAIL";
        code = failed;
        revert Code(failed);
    }

    function read() external view returns (bytes32, bytes32) {
        return (code, acc);
    }
}
