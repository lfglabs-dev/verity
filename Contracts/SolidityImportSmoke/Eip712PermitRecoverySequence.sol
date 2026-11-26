// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// A synthetic typed-data permit verifier. The domain name and version are
/// storage strings, hashed through `bytes(...)`; the digest uses
/// `keccak256(abi.encode(...))` and `abi.encodePacked("\x19\x01", ...)`; and
/// signature recovery uses the global `ecrecover` with the strict checks a
/// reusable ECDSA helper applies: low `s`, `v` in {27, 28}, non-zero `r` and
/// `s`, and a recovered address that is not zero.
contract PermitRecoveryFixture {
    bytes32 public constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 public constant PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");
    bytes32 private constant HALF_ORDER =
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0;

    string private _name = "SyntheticPermit";
    string private _version = "1";

    mapping(address => uint256) public nonces;
    mapping(address => mapping(address => uint256)) public allowance;
    address public lastSigner;
    uint256 public recoveries;

    function _EIP712NameHash() internal view returns (bytes32) {
        return keccak256(bytes(_name));
    }

    function _EIP712VersionHash() internal view returns (bytes32) {
        return keccak256(bytes(_version));
    }

    function domainSeparator() public view returns (bytes32) {
        return keccak256(
            abi.encode(
                DOMAIN_TYPEHASH,
                _EIP712NameHash(),
                _EIP712VersionHash(),
                block.chainid,
                address(this)
            )
        );
    }

    function hashPermit(
        address owner,
        address spender,
        uint256 value,
        uint256 nonce,
        uint256 deadline
    ) public pure returns (bytes32) {
        return keccak256(abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline));
    }

    function hashTypedData(bytes32 structHash) public view returns (bytes32) {
        return keccak256(abi.encodePacked("\x19\x01", domainSeparator(), structHash));
    }

    /// Error codes: 0 none, 1 invalid signature, 2 invalid `v`, 3 high `s`.
    function tryRecover(bytes32 digest, uint8 v, bytes32 r, bytes32 s)
        public
        pure
        returns (address, uint8)
    {
        if (uint256(s) > uint256(HALF_ORDER)) {
            return (address(0), 3);
        }
        if (v != 27 && v != 28) {
            return (address(0), 2);
        }
        if (r == bytes32(0) || s == bytes32(0)) {
            return (address(0), 1);
        }
        address signer = ecrecover(digest, v, r, s);
        if (signer == address(0)) {
            return (address(0), 1);
        }
        return (signer, 0);
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
        uint256 nonce = nonces[owner];
        bytes32 structHash = hashPermit(owner, spender, value, nonce, deadline);
        bytes32 digest = hashTypedData(structHash);
        (address signer, uint8 err) = tryRecover(digest, v, r, s);
        require(err == 0 && signer == owner, "INVALID_SIGNER");
        nonces[owner] = nonce + 1;
        allowance[owner][spender] = value;
        lastSigner = signer;
        recoveries += 1;
    }
}
