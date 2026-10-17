// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Representation instrument; not an imported function or allocator proof.
contract BytesObjectMemoryFixture {
    function inspect(bytes calldata payload, bytes calldata nextPayload) external pure {
        bytes memory first = abi.encodePacked(payload);
        bytes memory aliasOfFirst = first;
        bytes memory second = abi.encodePacked(nextPayload);
        require(keccak256(second) != bytes32(0), "second object hash");
        assembly ("memory-safe") {
            let rounded := and(add(mload(aliasOfFirst), 31), not(31))
            return(aliasOfFirst, add(32, rounded))
        }
    }
}
