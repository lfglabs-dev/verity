// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

struct Authorization {
    address authorizer;
    address authorized;
    bool isAuthorized;
    uint256 nonce;
    uint256 deadline;
}

struct Signature {
    uint8 v;
    bytes32 r;
    bytes32 s;
}

interface IAuthorizerHook {
    function onAuthorize(Authorization calldata authorization, uint8 v) external returns (bytes4);
}

library Math {
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        return (a & b) + (a ^ b) / 2;
    }
}

library StorageSlot {
    struct AddressSlot {
        address value;
    }

    struct Bytes32Slot {
        bytes32 value;
    }

    struct Uint256Slot {
        uint256 value;
    }

    function getAddressSlot(bytes32 slot) internal pure returns (AddressSlot storage r) {
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
}

library Arrays {
    using StorageSlot for bytes32;

    function findUpperBound(uint256[] storage array, uint256 element) internal view returns (uint256) {
        uint256 low = 0;
        uint256 high = array.length;

        if (high == 0) {
            return 0;
        }

        while (low < high) {
            uint256 mid = Math.average(low, high);

            if (unsafeAccess(array, mid).value > element) {
                high = mid;
            } else {
                low = mid + 1;
            }
        }

        if (low > 0 && unsafeAccess(array, low - 1).value == element) {
            return low - 1;
        } else {
            return low;
        }
    }

    function unsafeAccess(address[] storage arr, uint256 pos) internal pure returns (StorageSlot.AddressSlot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getAddressSlot();
    }

    function unsafeAccess(bytes32[] storage arr, uint256 pos) internal pure returns (StorageSlot.Bytes32Slot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getBytes32Slot();
    }

    function unsafeAccess(uint256[] storage arr, uint256 pos) internal pure returns (StorageSlot.Uint256Slot storage) {
        bytes32 slot;
        assembly ("memory-safe") {
            mstore(0, arr.slot)
            slot := add(keccak256(0, 0x20), pos)
        }
        return slot.getUint256Slot();
    }

    function unsafeMemoryAccess(address[] memory arr, uint256 pos) internal pure returns (address res) {
        assembly ("memory-safe") {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }

    function unsafeMemoryAccess(bytes32[] memory arr, uint256 pos) internal pure returns (bytes32 res) {
        assembly ("memory-safe") {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }

    function unsafeMemoryAccess(uint256[] memory arr, uint256 pos) internal pure returns (uint256 res) {
        assembly ("memory-safe") {
            res := mload(add(add(arr, 0x20), mul(pos, 0x20)))
        }
    }
}

library EnumerableSet {
    struct Set {
        bytes32[] _values;
        mapping(bytes32 => uint256) _positions;
    }

    struct Bytes32Set {
        Set _inner;
    }

    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            set._positions[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    function _remove(Set storage set, bytes32 value) private returns (bool) {
        uint256 position = set._positions[value];

        if (position != 0) {
            uint256 valueIndex = position - 1;
            uint256 lastIndex = set._values.length - 1;

            if (valueIndex != lastIndex) {
                bytes32 lastValue = Arrays.unsafeAccess(set._values, lastIndex).value;
                Arrays.unsafeAccess(set._values, valueIndex).value = lastValue;
                set._positions[lastValue] = position;
            }

            set._values.pop();
            delete set._positions[value];

            return true;
        } else {
            return false;
        }
    }

    function _clear(Set storage set) private {
        uint256 len = set._values.length;
        for (uint256 i = 0; i < len; ++i) {
            delete set._positions[Arrays.unsafeAccess(set._values, i).value];
        }
        delete set._values;
    }

    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._positions[value] != 0;
    }

    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        return set._values[index];
    }

    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    function clear(Bytes32Set storage set) internal {
        _clear(set._inner);
    }

    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }
}

library EnumerableMap {
    using EnumerableSet for EnumerableSet.Bytes32Set;

    error EnumerableMapNonexistentKey(bytes32 key);

    struct Bytes32ToBytes32Map {
        EnumerableSet.Bytes32Set _keys;
        mapping(bytes32 => bytes32) _values;
    }

    struct Bytes32ToUintMap {
        Bytes32ToBytes32Map _inner;
    }

    struct AddressToUintMap {
        Bytes32ToBytes32Map _inner;
    }

    function set(Bytes32ToBytes32Map storage map, bytes32 key, bytes32 value) internal returns (bool) {
        map._values[key] = value;
        return map._keys.add(key);
    }

    function remove(Bytes32ToBytes32Map storage map, bytes32 key) internal returns (bool) {
        delete map._values[key];
        return map._keys.remove(key);
    }

    function clear(Bytes32ToBytes32Map storage map) internal {
        uint256 len = length(map);
        for (uint256 i = 0; i < len; ++i) {
            delete map._values[map._keys.at(i)];
        }
        map._keys.clear();
    }

    function contains(Bytes32ToBytes32Map storage map, bytes32 key) internal view returns (bool) {
        return map._keys.contains(key);
    }

    function length(Bytes32ToBytes32Map storage map) internal view returns (uint256) {
        return map._keys.length();
    }

    function at(Bytes32ToBytes32Map storage map, uint256 index) internal view returns (bytes32 key, bytes32 value) {
        bytes32 atKey = map._keys.at(index);
        return (atKey, map._values[atKey]);
    }

    function tryGet(Bytes32ToBytes32Map storage map, bytes32 key) internal view returns (bool exists, bytes32 value) {
        bytes32 val = map._values[key];
        if (val == bytes32(0)) {
            return (contains(map, key), bytes32(0));
        } else {
            return (true, val);
        }
    }

    function get(Bytes32ToBytes32Map storage map, bytes32 key) internal view returns (bytes32) {
        bytes32 value = map._values[key];
        if (value == 0 && !contains(map, key)) {
            revert EnumerableMapNonexistentKey(key);
        }
        return value;
    }

    function set(Bytes32ToUintMap storage map, bytes32 key, uint256 value) internal returns (bool) {
        return set(map._inner, key, bytes32(value));
    }

    function remove(Bytes32ToUintMap storage map, bytes32 key) internal returns (bool) {
        return remove(map._inner, key);
    }

    function clear(Bytes32ToUintMap storage map) internal {
        clear(map._inner);
    }

    function contains(Bytes32ToUintMap storage map, bytes32 key) internal view returns (bool) {
        return contains(map._inner, key);
    }

    function length(Bytes32ToUintMap storage map) internal view returns (uint256) {
        return length(map._inner);
    }

    function at(Bytes32ToUintMap storage map, uint256 index) internal view returns (bytes32 key, uint256 value) {
        (bytes32 k, bytes32 v) = at(map._inner, index);
        return (k, uint256(v));
    }

    function tryGet(Bytes32ToUintMap storage map, bytes32 key) internal view returns (bool exists, uint256 value) {
        (bool ok, bytes32 v) = tryGet(map._inner, key);
        return (ok, uint256(v));
    }

    function get(Bytes32ToUintMap storage map, bytes32 key) internal view returns (uint256) {
        return uint256(get(map._inner, key));
    }

    function set(AddressToUintMap storage map, address key, uint256 value) internal returns (bool) {
        return set(map._inner, bytes32(uint256(uint160(key))), bytes32(value));
    }

    function remove(AddressToUintMap storage map, address key) internal returns (bool) {
        return remove(map._inner, bytes32(uint256(uint160(key))));
    }

    function contains(AddressToUintMap storage map, address key) internal view returns (bool) {
        return contains(map._inner, bytes32(uint256(uint160(key))));
    }

    function length(AddressToUintMap storage map) internal view returns (uint256) {
        return length(map._inner);
    }

    function tryGet(AddressToUintMap storage map, address key) internal view returns (bool exists, uint256 value) {
        (bool ok, bytes32 v) = tryGet(map._inner, bytes32(uint256(uint160(key))));
        return (ok, uint256(v));
    }
}

contract EcrecoverAuthorizer {
    bytes32 public constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(uint256 chainId,address verifyingContract)");
    bytes32 public constant AUTHORIZATION_TYPEHASH =
        keccak256("Authorization(address authorizer,address authorized,bool isAuthorized,uint256 nonce,uint256 deadline)");

    error AlreadySet();
    error InvalidNonce(uint256 expectedNonce, uint256 providedNonce);
    error AuthorizationExpired(uint256 deadline, uint256 currentTimestamp);

    mapping(address => mapping(address => bool)) public isAuthorized;
    mapping(address => uint256) public nonces;

    function domainSeparator() public view returns (bytes32) {
        return keccak256(abi.encode(DOMAIN_TYPEHASH, block.chainid, address(this)));
    }

    function hashAuthorization(Authorization memory authorization) public pure returns (bytes32) {
        return keccak256(abi.encode(AUTHORIZATION_TYPEHASH, authorization));
    }

    function hashTypedData(Authorization memory authorization) public view returns (bytes32) {
        return keccak256(
            bytes.concat("\x19\x01", domainSeparator(), keccak256(abi.encode(AUTHORIZATION_TYPEHASH, authorization)))
        );
    }
}

contract SequenceFixture is EcrecoverAuthorizer {
    using Arrays for uint256[];
    using EnumerableMap for EnumerableMap.Bytes32ToUintMap;
    using EnumerableMap for EnumerableMap.AddressToUintMap;

    error ERC1155InvalidArrayLength(uint256 idsLength, uint256 valuesLength);

    EnumerableMap.Bytes32ToUintMap private digestScores;
    EnumerableMap.AddressToUintMap private authorizerCredits;
    uint256[] private scoreCheckpoints;
    Authorization[] public authorizationHistory;
    Authorization public latestAuthorization;
    mapping(address => Authorization) public lastAuthorizationOf;
    bytes32 private lastDigest;
    uint256 private totalAuthorizedOps;

    function _scoreCheckpointSlot(uint256 pos) internal pure returns (StorageSlot.Uint256Slot storage r) {
        assembly ("memory-safe") {
            mstore(0, scoreCheckpoints.slot)
            r.slot := add(keccak256(0, 0x20), pos)
        }
    }

    function _scoreCheckpointsSlotWord() internal pure returns (uint256 slotWord) {
        assembly ("memory-safe") {
            slotWord := scoreCheckpoints.slot
        }
    }

    function _buildLocalAuthorization(
        address authorizer,
        address authorized,
        bool flag,
        uint256 nonce,
        uint256 deadline
    ) internal pure returns (Authorization memory) {
        return Authorization({
            authorizer: authorizer,
            authorized: authorized,
            isAuthorized: flag,
            nonce: nonce,
            deadline: deadline
        });
    }

    function change(uint256 input) external returns (uint256) {
        require(input != 20, "authorizer rollback");
        uint256 mode = input % 5;
        address authorizer = address(uint160(0x3000 + (input % 3)));
        address authorized = address(uint160(0x4000 + ((input >> 1) % 3)));
        uint256 curNonce = nonces[authorizer];
        bool flag = (input & 1) == 0;
        uint256 deadline = block.timestamp + 100 + (input % 50);

        Authorization memory auth = _buildLocalAuthorization(authorizer, authorized, flag, curNonce, deadline);
        Signature memory sig = Signature({
            v: uint8(27 + (input & 1)),
            r: keccak256(abi.encode(input, authorizer)),
            s: keccak256(abi.encode(authorized, curNonce))
        });

        bytes32 digest = hashTypedData(auth);
        bytes32 bundleHash = keccak256(abi.encode(auth, sig));
        bytes32 selHash = keccak256(abi.encodeWithSelector(IAuthorizerHook.onAuthorize.selector, auth, sig.v));
        bytes32 sigHash = keccak256(
            abi.encodeWithSignature(
                "onAuthorize((address,address,bool,uint256,uint256),uint8)",
                auth,
                sig.v
            )
        );
        bytes32 callHash = keccak256(abi.encodeCall(IAuthorizerHook.onAuthorize, (auth, sig.v)));
        require(selHash == sigHash && selHash == callHash, "selector encoding mismatch");

        if (mode == 0) {
            isAuthorized[authorizer][authorized] = flag;
            nonces[authorizer] = curNonce + 1;
            latestAuthorization = auth;
            lastAuthorizationOf[authorizer] = auth;
            authorizationHistory.push(auth);
            uint256 scoreVal = ((uint256(digest) ^ uint256(bundleHash)) & 0xffff) + 10;
            digestScores.set(digest, scoreVal);
            authorizerCredits.set(authorizer, scoreVal + curNonce);
            uint256 nextCheckpoint = scoreCheckpoints.length == 0
                ? scoreVal
                : _scoreCheckpointSlot(scoreCheckpoints.length - 1).value + (scoreVal & 0xff) + 1;
            scoreCheckpoints.push(nextCheckpoint);
        } else if (mode == 1) {
            authorizationHistory.push(auth);
            Authorization storage pushed = authorizationHistory[authorizationHistory.length - 1];
            pushed.deadline = deadline + 7;
            latestAuthorization = pushed;
            lastAuthorizationOf[authorizer] = auth;
            nonces[authorizer] += 2;
            uint256 cpVal = scoreCheckpoints.length == 0
                ? 25
                : _scoreCheckpointSlot(scoreCheckpoints.length - 1).value + 25;
            scoreCheckpoints.push(cpVal);
            _scoreCheckpointSlot(scoreCheckpoints.length - 1).value = cpVal + _scoreCheckpointsSlotWord();
            digestScores.set(bundleHash, cpVal);
        } else if (mode == 2) {
            if (authorizationHistory.length > 0) {
                Authorization memory tail = authorizationHistory[authorizationHistory.length - 1];
                latestAuthorization = tail;
                if (authorizationHistory.length > 1) {
                    authorizationHistory.pop();
                }
            }
            if (digestScores.length() > 0) {
                (bytes32 firstKey, uint256 firstVal) = digestScores.at(0);
                if ((input & 2) == 0) {
                    digestScores.remove(firstKey);
                } else {
                    digestScores.set(firstKey, firstVal + 9);
                }
            }
        } else if (mode == 3) {
            uint256[] memory ids = new uint256[](2);
            address[] memory accts = new address[](2);
            ids[0] = (input & 0xff) + 1;
            ids[1] = ((input >> 4) & 0xff) + 2;
            accts[0] = authorizer;
            accts[1] = authorized;
            uint256 memSum = Arrays.unsafeMemoryAccess(ids, 0) + Arrays.unsafeMemoryAccess(ids, 1);
            address picked = Arrays.unsafeMemoryAccess(accts, input & 1);
            authorizerCredits.set(picked, memSum);
            uint256 ub = scoreCheckpoints.findUpperBound(memSum);
            totalAuthorizedOps += ub + memSum;
        } else {
            if (digestScores.length() > 2) {
                digestScores.clear();
            }
            authorizerCredits.remove(authorizer);
            isAuthorized[authorizer][authorized] = !isAuthorized[authorizer][authorized];
        }

        uint256 ubNow = scoreCheckpoints.findUpperBound((input & 0x3ff) + 1);
        (, uint256 creditNow) = authorizerCredits.tryGet(authorizer);
        uint256 metric = ubNow + creditNow + digestScores.length() + authorizationHistory.length +
            (uint256(selHash) & 0xff) + _scoreCheckpointsSlotWord();
        totalAuthorizedOps += 1;
        lastDigest = keccak256(abi.encode(digest, bundleHash, metric));
        return totalAuthorizedOps + metric;
    }

    function verifyAndRecord(
        Authorization calldata authorization,
        Signature calldata signature
    ) external returns (Authorization memory) {
        if (block.timestamp > authorization.deadline) {
            revert AuthorizationExpired(authorization.deadline, block.timestamp);
        }
        uint256 expectedNonce = nonces[authorization.authorizer];
        if (authorization.nonce != expectedNonce) {
            revert InvalidNonce(expectedNonce, authorization.nonce);
        }
        bytes32 structHash = keccak256(abi.encode(AUTHORIZATION_TYPEHASH, authorization));
        bytes32 pairHash = keccak256(abi.encode(authorization, signature));
        bytes32 callHash = keccak256(abi.encodeCall(IAuthorizerHook.onAuthorize, (authorization, signature.v)));
        bytes32 digest = keccak256(bytes.concat("\x19\x01", domainSeparator(), structHash, pairHash, callHash));

        nonces[authorization.authorizer] = expectedNonce + 1;
        isAuthorized[authorization.authorizer][authorization.authorized] = authorization.isAuthorized;
        latestAuthorization = authorization;
        lastAuthorizationOf[authorization.authorizer] = authorization;
        authorizationHistory.push(authorization);
        digestScores.set(digest, uint256(signature.v) + authorization.nonce);
        lastDigest = digest;
        totalAuthorizedOps += 1;
        return authorization;
    }

    function batchCheckAndSum(
        address[] calldata accounts,
        uint256[] calldata ids
    ) external view returns (uint256, uint256) {
        if (accounts.length != ids.length) {
            revert ERC1155InvalidArrayLength(ids.length, accounts.length);
        }
        uint256 accSum = 0;
        uint256 ubSum = 0;
        for (uint256 i = 0; i < accounts.length; ++i) {
            (, uint256 credit) = authorizerCredits.tryGet(accounts[i]);
            accSum += credit + ids[i] + (isAuthorized[accounts[i]][msg.sender] ? 100 : 0);
            ubSum += scoreCheckpoints.findUpperBound(ids[i]);
        }
        return (accSum, ubSum + digestScores.length());
    }

    function fail() external {
        uint256[] memory a = new uint256[](1);
        uint256[] memory b = new uint256[](2);
        a[0] = 11;
        b[0] = 22;
        b[1] = 33;
        totalAuthorizedOps += 99;
        if (a.length != b.length) {
            revert ERC1155InvalidArrayLength(a.length, b.length);
        }
    }

    function read() external view returns (uint256, uint256, uint256, uint256) {
        address a0 = address(uint160(0x3000));
        address b0 = address(uint160(0x4000));
        (, uint256 c0) = authorizerCredits.tryGet(a0);
        uint256 topCp = scoreCheckpoints.length == 0
            ? 0
            : _scoreCheckpointSlot(scoreCheckpoints.length - 1).value;
        return (
            totalAuthorizedOps + (isAuthorized[a0][b0] ? 1000 : 0) + nonces[a0],
            uint256(lastDigest) & 0xffffffffffffffff,
             (digestScores.length() << 32) | (authorizationHistory.length << 16) | (scoreCheckpoints.length & 0xffff),
            c0 + topCp + latestAuthorization.nonce + lastAuthorizationOf[a0].deadline
        );
    }
}
