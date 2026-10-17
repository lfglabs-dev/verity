// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Instrument for IdLib's exact 11-byte SSTORE2 initcode. Not importer support.
contract DeploymentFixture {
    event Deployed(address indexed account);

    function deploy(bytes32 salt, bytes calldata payload, bool failAfter)
        external returns (address account)
    {
        bytes memory creationCode = abi.encodePacked(hex"600b380380600b5f395ff3", payload);
        assembly ("memory-safe") {
            account := create2(0, add(creationCode, 32), mload(creationCode), salt)
        }
        require(account != address(0), "deployment failed");
        emit Deployed(account);
        require(!failAfter, "parent rollback");
    }
}
