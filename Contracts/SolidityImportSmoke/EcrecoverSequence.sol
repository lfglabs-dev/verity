// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Solidity's global `ecrecover` builtin: direct recovery, a pure signer check, an
/// explicit `uint8` conversion of the `v` argument, left-to-right argument evaluation
/// against a later argument that writes the storage an earlier argument reads, and an
/// EIP-2612-style permit whose digest hashes the consumed nonce.
contract EcrecoverFixture {
    bytes32 public constant PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    mapping(address => uint256) public nonces;
    mapping(address => mapping(address => uint256)) public allowance;
    bytes32 public storedDigest;
    address public lastRecovered;
    uint256 public recoveries;

    function domainSeparator() public view returns (bytes32) {
        return keccak256(abi.encode(
            keccak256("EIP712Domain(uint256 chainId,address verifyingContract)"),
            block.chainid,
            address(this)));
    }

    function recover(bytes32 digest, uint8 v, bytes32 r, bytes32 s) external returns (address) {
        address recovered = ecrecover(digest, v, r, s);
        lastRecovered = recovered;
        recoveries += 1;
        return recovered;
    }

    function verify(bytes32 digest, uint8 v, bytes32 r, bytes32 s, address expected)
        external
        pure
        returns (bool)
    {
        address recovered = ecrecover(digest, v, r, s);
        return recovered != address(0) && recovered == expected;
    }

    function recoverWide(bytes32 digest, uint256 vWord, bytes32 r, bytes32 s)
        external
        pure
        returns (address)
    {
        return ecrecover(digest, uint8(vWord), r, s);
    }

    function setDigest(bytes32 digest) external {
        storedDigest = digest;
    }

    function _replaceDigest(bytes32 next) internal returns (bytes32) {
        storedDigest = next;
        return next;
    }

    /// The first argument reads `storedDigest` before the last one overwrites it.
    function recoverOrdered(uint8 v, bytes32 r, bytes32 s) external returns (address) {
        return ecrecover(storedDigest, v, r, _replaceDigest(s));
    }

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external {
        require(deadline >= block.timestamp, "PERMIT_DEADLINE_EXPIRED");
        unchecked {
            uint256 nonce = nonces[owner]++;
            address recoveredAddress = ecrecover(
                keccak256(
                    abi.encodePacked(
                        "\x19\x01",
                        domainSeparator(),
                        keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline))
                    )
                ),
                v,
                r,
                s
            );
            require(recoveredAddress != address(0) && recoveredAddress == owner, "INVALID_SIGNER");
            allowance[recoveredAddress][spender] = value;
        }
    }
}
