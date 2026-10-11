// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library MathSlice40 {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + (a ^ b) / 2;
    }

    function sqrt(uint256 a) internal pure returns (uint256) {
        unchecked {
            if (a <= 1) {
                return a;
            }
            uint256 aa = a;
            uint256 xn = 1;
            if (aa >= (1 << 128)) {
                aa >>= 128;
                xn <<= 64;
            }
            if (aa >= (1 << 64)) {
                aa >>= 64;
                xn <<= 32;
            }
            if (aa >= (1 << 32)) {
                aa >>= 32;
                xn <<= 16;
            }
            if (aa >= (1 << 16)) {
                aa >>= 16;
                xn <<= 8;
            }
            if (aa >= (1 << 8)) {
                aa >>= 8;
                xn <<= 4;
            }
            if (aa >= (1 << 4)) {
                aa >>= 4;
                xn <<= 2;
            }
            if (aa >= (1 << 2)) {
                xn <<= 1;
            }
            xn = (3 * xn) >> 1;
            xn = (xn + a / xn) >> 1;
            xn = (xn + a / xn) >> 1;
            xn = (xn + a / xn) >> 1;
            xn = (xn + a / xn) >> 1;
            xn = (xn + a / xn) >> 1;
            xn = (xn + a / xn) >> 1;
            return xn - (xn > a / xn ? 1 : 0);
        }
    }
}

library StorageSlotSlice40 {
    struct AddressSlot {
        address value;
    }

    struct BooleanSlot {
        bool value;
    }

    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    struct StringSlot {
        string value;
    }

    struct BytesSlot {
        bytes value;
    }

    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getBooleanSlot(bytes32 slot) internal pure returns (BooleanSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getBytes32Slot(bytes32 slot) internal pure returns (Bytes32Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getUint256Slot(bytes32 slot) internal pure returns (Uint256Slot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getStringSlot(bytes32 slot) internal pure returns (StringSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getStringSlot(string storage store) internal pure returns (StringSlot storage r) {
        assembly ("memory-safe") {
            r.slot := store.slot
        }
    }

    function getBytesSlot(bytes32 slot) internal pure returns (BytesSlot storage r) {
        assembly ("memory-safe") {
            r.slot := slot
        }
    }

    function getBytesSlot(bytes storage store) internal pure returns (BytesSlot storage r) {
        assembly ("memory-safe") {
            r.slot := store.slot
        }
    }
}

library ECDSASlice40 {
    enum RecoverError {
        NoError,
        InvalidSignature,
        InvalidSignatureLength,
        InvalidSignatureS
    }

    error ECDSAInvalidSignature();
    error ECDSAInvalidSignatureLength(uint256 length);
    error ECDSAInvalidSignatureS(bytes32 s);

    function tryRecover(bytes32 hash, bytes memory signature) internal pure returns (address, RecoverError, bytes32) {
        uint256 sigLen;
        assembly ("memory-safe") {
            sigLen := mload(signature)
        }
        if (sigLen == 65) {
            bytes32 r;
            bytes32 s;
            uint8 v;
            assembly ("memory-safe") {
                r := mload(add(signature, 0x20))
                s := mload(add(signature, 0x40))
                v := byte(0, mload(add(signature, 0x60)))
            }
            return tryRecover(hash, v, r, s);
        } else {
            return (address(0), RecoverError.InvalidSignatureLength, bytes32(sigLen));
        }
    }

    function recover(bytes32 hash, bytes memory signature) internal pure returns (address) {
        (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, signature);
        _throwError(error, errorArg);
        return recovered;
    }

    function tryRecover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address, RecoverError, bytes32) {
        unchecked {
            bytes32 s = vs & bytes32(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
            uint8 v = uint8((uint256(vs) >> 255) + 27);
            return tryRecover(hash, v, r, s);
        }
    }

    function recover(bytes32 hash, bytes32 r, bytes32 vs) internal pure returns (address) {
        (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, r, vs);
        _throwError(error, errorArg);
        return recovered;
    }

    function tryRecover(
        bytes32 hash,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal pure returns (address, RecoverError, bytes32) {
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return (address(0), RecoverError.InvalidSignatureS, s);
        }
        if ((v != 27 && v != 28) || r == bytes32(0) || s == bytes32(0)) {
            return (address(0), RecoverError.InvalidSignature, bytes32(0));
        }
        address signer = address(uint160(uint256(keccak256(abi.encode(hash, v, r, s)))));
        if (signer == address(0)) {
            return (address(0), RecoverError.InvalidSignature, bytes32(0));
        }
        return (signer, RecoverError.NoError, bytes32(0));
    }

    function recover(bytes32 hash, uint8 v, bytes32 r, bytes32 s) internal pure returns (address) {
        (address recovered, RecoverError error, bytes32 errorArg) = tryRecover(hash, v, r, s);
        _throwError(error, errorArg);
        return recovered;
    }

    function _throwError(RecoverError error, bytes32 errorArg) private pure {
        if (error == RecoverError.NoError) {
            return;
        } else if (error == RecoverError.InvalidSignature) {
            revert ECDSAInvalidSignature();
        } else if (error == RecoverError.InvalidSignatureLength) {
            revert ECDSAInvalidSignatureLength(uint256(errorArg));
        } else if (error == RecoverError.InvalidSignatureS) {
            revert ECDSAInvalidSignatureS(errorArg);
        }
    }
}

library MerkleProofSlice40 {
    function verify(bytes32[] memory proof, bytes32 root, bytes32 leaf) internal pure returns (bool) {
        return processProof(proof, leaf) == root;
    }

    function processProof(bytes32[] memory proof, bytes32 leaf) internal pure returns (bytes32) {
        bytes32 computedHash = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            computedHash = _hashPair(computedHash, proof[i]);
        }
        return computedHash;
    }

    function _hashPair(bytes32 a, bytes32 b) private pure returns (bytes32 value) {
        if (a < b) {
            assembly ("memory-safe") {
                mstore(0x00, a)
                mstore(0x20, b)
                value := keccak256(0x00, 0x40)
            }
        } else {
            assembly ("memory-safe") {
                mstore(0x00, b)
                mstore(0x20, a)
                value := keccak256(0x00, 0x40)
            }
        }
    }
}

library CheckpointsSlice40 {
    struct Trace224 {
        Checkpoint224[] _checkpoints;
    }

    struct Checkpoint224 {
        uint32 _key;
        uint224 _value;
    }

    error CheckpointUnorderedInsertion();

    function push(Trace224 storage self, uint32 key, uint224 value) internal returns (uint224, uint224) {
        return _insert(self._checkpoints, key, value);
    }

    function lowerLookup(Trace224 storage self, uint32 key) internal view returns (uint224) {
        uint256 len = self._checkpoints.length;
        uint256 pos = _lowerBinaryLookup(self._checkpoints, key, 0, len);
        return pos == len ? 0 : _unsafeAccess(self._checkpoints, pos)._value;
    }

    function upperLookupRecent(Trace224 storage self, uint32 key) internal view returns (uint224) {
        uint256 len = self._checkpoints.length;
        uint256 low = 0;
        uint256 high = len;
        if (len > 5) {
            uint256 mid = len - MathSlice40.sqrt(len);
            if (key < _unsafeAccess(self._checkpoints, mid)._key) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        uint256 pos = _upperBinaryLookup(self._checkpoints, key, low, high);
        return pos == 0 ? 0 : _unsafeAccess(self._checkpoints, pos - 1)._value;
    }

    function latest(Trace224 storage self) internal view returns (uint224) {
        uint256 pos = self._checkpoints.length;
        return pos == 0 ? 0 : _unsafeAccess(self._checkpoints, pos - 1)._value;
    }

    function length(Trace224 storage self) internal view returns (uint256) {
        return self._checkpoints.length;
    }

    function _insert(
        Checkpoint224[] storage self,
        uint32 key,
        uint224 value
    ) private returns (uint224, uint224) {
        uint256 pos = self.length;
        if (pos > 0) {
            Checkpoint224 memory last = _unsafeAccess(self, pos - 1);
            if (last._key > key) {
                revert CheckpointUnorderedInsertion();
            }
            if (last._key == key) {
                _unsafeAccess(self, pos - 1)._value = value;
                return (last._value, value);
            }
        }
        self.push(Checkpoint224({ _key: key, _value: value }));
        return (pos == 0 ? 0 : _unsafeAccess(self, pos - 1)._value, value);
    }

    function _upperBinaryLookup(
        Checkpoint224[] storage self,
        uint32 key,
        uint256 low,
        uint256 high
    ) private view returns (uint256) {
        while (low < high) {
            uint256 mid = MathSlice40.average(low, high);
            if (_unsafeAccess(self, mid)._key > key) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        return high;
    }

    function _lowerBinaryLookup(
        Checkpoint224[] storage self,
        uint32 key,
        uint256 low,
        uint256 high
    ) private view returns (uint256) {
        while (low < high) {
            uint256 mid = MathSlice40.average(low, high);
            if (_unsafeAccess(self, mid)._key < key) {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        return high;
    }

    function _unsafeAccess(
        Checkpoint224[] storage self,
        uint256 pos
    ) private pure returns (Checkpoint224 storage result) {
        assembly ("memory-safe") {
            mstore(0, self.slot)
            result.slot := add(keccak256(0, 0x20), pos)
        }
    }
}

contract SequenceFixture {
    using StorageSlotSlice40 for bytes32;
    using CheckpointsSlice40 for CheckpointsSlice40.Trace224;

    bytes32 private constant RAW_LABEL_SLOT =
        0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc;
    bytes32 private constant RAW_PAYLOAD_SLOT =
        0xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103;

    event SignatureCheckpointRecorded(
        address indexed signer,
        uint256 indexed key,
        uint256 value,
        bytes32 merkleLeaf,
        uint256 payloadLen
    );

    CheckpointsSlice40.Trace224 private _trace;
    string private _fallbackLabel;
    uint256 private _totalWeight;
    bytes32 private _lastRecoveredHash;

    function recoverFromBytes(bytes32 hash, bytes memory signature) public pure returns (address) {
        return ECDSASlice40.recover(hash, signature);
    }

    function recoverFromCompact(bytes32 hash, bytes32 r, bytes32 vs) public pure returns (address) {
        return ECDSASlice40.recover(hash, r, vs);
    }

    function verifyMerkle(bytes32[] memory proof, bytes32 root, bytes32 leaf) public pure returns (bool) {
        return MerkleProofSlice40.verify(proof, root, leaf);
    }

    function rawSlotLabel() public view returns (string memory) {
        return RAW_LABEL_SLOT.getStringSlot().value;
    }

    function rawSlotPayload() public view returns (bytes memory) {
        return RAW_PAYLOAD_SLOT.getBytesSlot().value;
    }

    function checkpointUpperRecent(uint32 key) public view returns (uint224) {
        return _trace.upperLookupRecent(key);
    }

    function change(uint256 input) external returns (uint256) {
        uint32 stepKey = uint32(_trace.length() * 10 + ((input & 7) + 1));
        uint224 stepVal = uint224(((input & 0xff) + 1) * 100);
        (, uint224 newVal) = _trace.push(stepKey, stepVal);

        bytes32 msgHash = keccak256(abi.encode(msg.sender, stepKey, newVal));
        bytes32 r = keccak256(abi.encode("R", input, stepKey));
        bytes32 s = bytes32(uint256(keccak256(abi.encode("S", input, stepVal))) &
            0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
        uint8 v = (input & 1) == 0 ? 27 : 28;
        bytes memory sig65 = abi.encodePacked(r, s, v);
        address signer1 = ECDSASlice40.recover(msgHash, sig65);

        bytes32 vs = s | (v == 28 ? bytes32(uint256(1) << 255) : bytes32(0));
        address signer2 = ECDSASlice40.recover(msgHash, r, vs);
        require(signer1 == signer2, "EMCS: signer mismatch");

        bytes memory badSig = abi.encodePacked(r, s);
        (, ECDSASlice40.RecoverError badErr, bytes32 badArg) = ECDSASlice40.tryRecover(msgHash, badSig);
        require(
            badErr == ECDSASlice40.RecoverError.InvalidSignatureLength && uint256(badArg) == 64,
            "EMCS: expected length 64 error"
        );

        StorageSlotSlice40.StringSlot storage labelSlot = RAW_LABEL_SLOT.getStringSlot();
        StorageSlotSlice40.BytesSlot storage payloadSlot = RAW_PAYLOAD_SLOT.getBytesSlot();
        if ((input & 2) == 0) {
            labelSlot.value = "ecdsa-merkle-short";
            payloadSlot.value = sig65;
        } else {
            labelSlot.value = "ecdsa-merkle-long-storage-slot-string-value-40";
            delete payloadSlot.value;
            payloadSlot.value = abi.encodePacked(msgHash, r);
        }
        StorageSlotSlice40.getStringSlot(_fallbackLabel).value = labelSlot.value;

        uint256 payloadLen = payloadSlot.value.length;
        uint224 recentVal = _trace.upperLookupRecent(stepKey);
        uint224 lowerVal = _trace.lowerLookup(stepKey > 2 ? stepKey - 2 : 0);

        bytes32 sibling = keccak256(bytes(labelSlot.value));
        bytes32 leaf = keccak256(abi.encode(signer1, recentVal, lowerVal));
        bytes32 pairRoot = leaf < sibling
            ? keccak256(abi.encodePacked(leaf, sibling))
            : keccak256(abi.encodePacked(sibling, leaf));

        emit SignatureCheckpointRecorded(signer1, uint256(stepKey), uint256(recentVal), pairRoot, payloadLen);

        unchecked {
            _totalWeight +=
                uint256(recentVal) +
                uint256(lowerVal) +
                payloadLen +
                bytes(_fallbackLabel).length +
                (uint256(uint160(signer1)) & 0xffff);
        }
        _lastRecoveredHash = pairRoot ^ bytes32(uint256(uint160(signer1)));
        require(input != 20, "EMCS: rollback");
        return _totalWeight;
    }

    function fail() external {
        RAW_LABEL_SLOT.getStringSlot().value = "reverted-slot";
        _totalWeight += 777;
        revert("EMCS: fail");
    }

    function read() external view returns (uint256, bytes32, uint256, uint256) {
        return (
            _totalWeight,
            _lastRecoveredHash,
            _trace.length(),
            RAW_PAYLOAD_SLOT.getBytesSlot().value.length
        );
    }
}
