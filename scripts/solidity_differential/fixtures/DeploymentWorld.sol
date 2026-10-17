// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Account-transition instrument, not an importer-supported fixture yet.
contract DeploymentWorldFixture {
    event Attempted(address indexed account);

    function deploy(bytes32 salt, bytes calldata payload, bool failAfter,
                    uint256 amount, bool requireSuccess) external returns (address account) {
        bytes memory creationCode = abi.encodePacked(hex"600b380380600b5f395ff3", payload);
        assembly ("memory-safe") {
            account := create2(amount, add(creationCode, 32), mload(creationCode), salt)
        }
        if (requireSuccess) require(account != address(0), "deployment failed");
        emit Attempted(account);
        require(!failAfter, "parent rollback");
    }
}
