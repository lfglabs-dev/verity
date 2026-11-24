// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// OpenZeppelin 5.7 `ECDSA`, the calldata-signature path quoted as is: `tryRecoverCalldata`
/// splits a 65-byte `bytes calldata` signature with Yul `calldataload` at `signature.offset`
/// (#2920), then `tryRecover(hash, v, r, s)` rejects high `s` and recovers through the
/// `ecrecover` precompile; `recoverCalldata` reverts with the library's custom errors.
library ECDSA {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS
    }

    /**
     * @dev The signature is invalid.
     */
    error ECDSAInvalidSignature();

    /**
     * @dev The signature has an invalid length.
     */
    error ECDSAInvalidSignatureLength(uint256 length);

    /**
     * @dev The signature has an S value that is in the upper half order.
     */
    error ECDSAInvalidSignatureS(bytes32 s);

    /**
     * @dev Variant of {tryRecover} that takes a signature in calldata
     */
    function tryRecoverCalldata(
        bytes32 hash,
        bytes calldata signature
    ) internal pure returns (address recovered, RecoverError err, bytes32 errArg) {
        if (signature.length == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            // ecrecover takes the signature parameters, calldata slices would work here, but are
            // significantly more expensive (length check) than using calldataload in assembly.
            assembly ("memory-safe") {
                r := calldataload(signature.offset)
                s := calldataload(add(signature.offset, 0x20))
                v := byte(0, calldataload(add(signature.offset, 0x40)))
            }
            return tryRecover(hash, v, r, s);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength, bytes32(signature.length));
        }
    }

    /**
     * @dev Variant of {recover} that takes a signature in calldata
     */
    function recoverCalldata(bytes32 hash, bytes calldata signature) internal pure returns (address) {
        (address recovered, RecoverError err, bytes32 errorArg) = tryRecoverCalldata(hash, signature);
        _throwError(err, errorArg);
        return recovered;
    }

    /**
     * @dev Overload of {ECDSA-tryRecover} that receives the `v`,
     * `r` and `s` signature fields separately.
     */
    function tryRecover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address recovered, RecoverError err, bytes32 errArg) {
        // EIP-2 still allows signature malleability for ecrecover(). Remove this possibility and make the signature
        // unique. Appendix F in the Ethereum Yellow paper (https://ethereum.github.io/yellowpaper/paper.pdf), defines
        // the valid range for s in (301): 0 < s < secp256k1n ÷ 2 + 1, and for v in (302): v ∈ {27, 28}. Most
        // signatures from current libraries generate a unique signature with an s-value in the lower half order.
        //
        // If your library generates malleable signatures, such as s-values in the upper range, calculate a new s-value
        // with 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 - s1 and flip v from 27 to 28 or
        // vice versa. If your library also generates signatures with 0/1 for v instead 27/28, add 27 to v to accept
        // these malleable signatures as well.
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS, s);
        }

        // If the signature is valid (and not malleable), return the signer address
        address signer = ecrecover(hash, v, r, s);
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature, bytes32(0));
        }

        return (signer, RecoverError.NoError, bytes32(0));
    }

    /**
     * @dev Optionally reverts with the corresponding custom error according to the `error` argument provided.
     */
    function _throwError(RecoverError err, bytes32 errorArg) private pure {
        if (err == RecoverError.NoError) {
            return; // no error: do nothing
        } else if (err == RecoverError.InvalidSignature) {
            revert ECDSAInvalidSignature();
        } else if (err == RecoverError.InvalidSignatureLength) {
            revert ECDSAInvalidSignatureLength(uint256(errorArg));
        } else if (err == RecoverError.InvalidSignatureS) {
            revert ECDSAInvalidSignatureS(errorArg);
        }
    }
}

/// Generic signature consumers over `bytes calldata`: direct recovery, the raw
/// `tryRecoverCalldata` triple, and a nonce-consuming signed approval whose signature is the
/// last argument, so a caller can end calldata right after its 65th byte.
contract SignatureCalldataFixture {
    mapping(address => uint256) public nonces;
    mapping(address => mapping(address => uint256)) public allowance;

    error InvalidSigner(address recovered, address owner);

    function recover(bytes32 hash, bytes calldata signature) external pure returns (address) {
        return ECDSA.recoverCalldata(hash, signature);
    }

    function tryRecover(bytes32 hash, bytes calldata signature)
        external
        pure
        returns (address recovered, uint8 err, bytes32 errArg)
    {
        ECDSA.RecoverError code;
        (recovered, code, errArg) = ECDSA.tryRecoverCalldata(hash, signature);
        err = uint8(code);
    }

    function approveBySig(address owner, address spender, uint256 value, bytes calldata signature) external {
        bytes32 digest = keccak256(abi.encode(address(this), owner, spender, value, nonces[owner]++));
        address recovered = ECDSA.recoverCalldata(digest, signature);
        if (recovered != owner) revert InvalidSigner(recovered, owner);
        allowance[owner][spender] = value;
    }
}
