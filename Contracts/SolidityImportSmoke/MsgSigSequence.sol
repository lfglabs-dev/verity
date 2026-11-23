// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IAccessGate {
    function permits(address user, address target, bytes4 functionSig) external view returns (bool);
}

contract SequenceFixture {
    mapping(bytes4 => uint256) private calls;
    mapping(address => mapping(bytes4 => uint256)) private perCaller;
    bytes32 private lastSig;
    bytes32 private callDigest;
    uint256 private total;

    error Rejected(bytes32 sig);
    event Called(bytes4 indexed sig, bytes4 raw, uint256 amount);

    modifier tracked() {
        calls[msg.sig] += 1;
        _;
    }

    function _selector() internal view returns (bytes4) {
        return msg.sig;
    }

    function _count(bytes4 key, uint256 x) internal returns (uint256) {
        perCaller[msg.sender][key] += x % 5 + 1;
        return perCaller[msg.sender][key];
    }

    function change(uint256 x) external tracked returns (uint256) {
        bytes4 s = _selector();
        lastSig = bytes32(s);
        total += uint256(uint32(s)) + (x % 1000);
        // Inline assembly sees `msg.sig` as solc leaves it on the stack: the selector word alone, even
        // when the argument bytes of calldata word 0 are nonzero.
        bytes4 stackSig = msg.sig;
        uint256 sigWord;
        assembly { sigWord := stackSig }
        total += sigWord % 65521;
        uint256 counted = _count(msg.sig, x);
        callDigest = keccak256(abi.encodeCall(IAccessGate.permits, (msg.sender, address(this), msg.sig)));
        emit Called(msg.sig, msg.sig, x);
        if (x % 7 == 3) {
            bytes32 rejected = bytes32(msg.sig);
            revert Rejected(rejected);
        }
        require(msg.sig == this.change.selector, "msg.sig mismatch");
        return calls[msg.sig] + total + counted;
    }

    function fail() external tracked {
        bytes32 failing = bytes32(_selector());
        revert Rejected(failing);
    }

    function read() external view returns (bytes4, bytes32, uint256, uint256, uint256, uint256, bytes32) {
        return (msg.sig, lastSig, calls[this.change.selector], calls[msg.sig], total,
            perCaller[msg.sender][this.change.selector], callDigest);
    }
}
