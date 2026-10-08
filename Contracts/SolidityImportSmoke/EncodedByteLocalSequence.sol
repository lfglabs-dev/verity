// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 indexed digest);

    function digest(uint256 input) internal pure returns (uint256) {
        bytes memory encoded = abi.encode(input);
        bytes memory prefixed = abi.encodePacked(hex"010203", encoded);
        bytes memory aliasBuffer = prefixed;
        bytes32 first = keccak256(aliasBuffer);
        bytes memory other = abi.encode(input, uint256(17));
        bytes32 second = keccak256(other);
        require(first == keccak256(prefixed), "buffer changed");
        return uint256(keccak256(abi.encode(first, second)));
    }

    function change(uint256 input) external returns (uint256) {
        bytes memory rootBytes = abi.encodePacked(hex"ff", abi.encode(input));
        uint256 result = digest(input);
        if (input % 2 == 0) {
            bytes memory branchBytes = abi.encodePacked(hex"", rootBytes);
            require(keccak256(branchBytes) == keccak256(rootBytes), "branch copy");
        } else {
            bytes memory branchBytes = abi.encodePacked(rootBytes, hex"");
            require(keccak256(branchBytes) == keccak256(rootBytes), "branch copy");
        }
        value = result;
        emit Changed(result);
        require(input != 20, "encoded rollback");
        return result;
    }

    function fail() external {
        value = digest(1);
        emit Changed(value);
        require(false, "encoded fail");
    }

    function read() external view returns (uint256) { return value; }
}
