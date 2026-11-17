// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    mapping(bytes4 => uint256) private calls;
    bytes32 private lastSig;
    uint256 private total;

    error Rejected(bytes32 sig);

    modifier tracked() {
        calls[msg.sig] += 1;
        _;
    }

    function _selector() internal view returns (bytes4) {
        return msg.sig;
    }

    function change(uint256 x) external tracked returns (uint256) {
        bytes4 s = _selector();
        lastSig = bytes32(s);
        total += uint256(uint32(s)) + (x % 1000);
        if (x % 7 == 3) {
            bytes32 rejected = bytes32(msg.sig);
            revert Rejected(rejected);
        }
        require(msg.sig == this.change.selector, "msg.sig mismatch");
        return calls[msg.sig] + total;
    }

    function fail() external tracked {
        bytes32 failing = bytes32(_selector());
        revert Rejected(failing);
    }

    function read() external view returns (bytes4, bytes32, uint256, uint256, uint256) {
        return (msg.sig, lastSig, calls[this.change.selector], calls[msg.sig], total);
    }
}
