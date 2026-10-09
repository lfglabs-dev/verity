// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    error StorageBytesBlocked(uint256 input, bytes32 digest, uint256 lengthMetric);
    event StorageBytesObserved(uint256 indexed totalScore, bytes32 digest, uint256 lengthMetric);

    string private _name;
    string private _symbol;
    bytes private _payload;
    uint256 private totalScore;
    bytes32 private lastDigest;
    uint256 private syncCount;

    modifier trackSync(uint256 delta) {
        syncCount += 1;
        _;
        totalScore += (delta & 0xffff) + bytes(_name).length + _payload.length;
    }

    function _initMeta(string memory name_, string memory symbol_) internal {
        _name = name_;
        _symbol = symbol_;
    }

    function change(uint256 input) external returns (uint256) {
        uint256 branch = input % 6;
        if (branch == 0) {
            _initMeta("Idle Credit Vault", "ICV");
            _payload = hex"1122334455";
        } else if (branch == 1) {
            bytes32 saltWord = bytes32(input ^ 0xdeadbeef);
            _name = "Pareto Credit Vault Tranche Alpha Series 01";
            _symbol = "PCV-ALPHA-LONG-SYMBOL-36-BYTES-TOTAL";
            _payload = abi.encodePacked(input, saltWord, hex"cafebabe01");
        } else if (branch == 2) {
            _name = "ShortVault";
            _symbol = "SV";
            _payload = abi.encode(input, uint256(77));
        } else if (branch == 3) {
            delete _name;
            delete _payload;
            _symbol = "";
        } else if (branch == 4) {
            _initMeta("Vault-Four", "V4");
            _name = _name;
            _payload = bytes(_payload);
        } else {
            _name = _symbol;
            _symbol = string.concat(_name, ":tag");
            _payload = bytes.concat(_payload, bytes32(input));
        }

        uint256 nameLen = bytes(_name).length;
        uint256 symLen = bytes(_symbol).length;
        uint256 payLen = _payload.length;
        uint256 totalLen = nameLen + symLen + payLen;
        bytes32 digest = keccak256(abi.encodePacked(_name, ":", _symbol, _payload, input));

        if (input == 21) {
            revert StorageBytesBlocked(input, digest, totalLen);
        }

        syncCount += 1;
        uint256 metric = totalLen + syncCount;
        totalScore += (uint256(digest) & 0xffffffff) + metric;
        lastDigest = digest;
        emit StorageBytesObserved(totalScore, lastDigest, metric);
        require(input != 20, "storage bytes rollback");
        return totalScore;
    }

    function syncStorage(
        string memory newName,
        bytes calldata newPayload,
        uint256 mode
    ) external trackSync(mode) returns (uint256) {
        uint256 kind = mode % 5;
        if (kind == 0) {
            _name = newName;
            _payload = newPayload;
        } else if (kind == 1) {
            _name = string.concat(newName, "-", _symbol);
            _payload = bytes.concat(_payload, newPayload);
        } else if (kind == 2) {
            _symbol = "PCV-TEMP-LONG-SYMBOL-TO-SHRINK-36-B";
            _symbol = newName;
            _name = _symbol;
            _payload = newPayload;
        } else if (kind == 3) {
            delete _name;
            _payload = newPayload;
        } else {
            _name = newName;
            delete _payload;
        }

        uint256 combinedLen = bytes(_name).length + bytes(_symbol).length + _payload.length;
        bytes32 digest = keccak256(abi.encodePacked(_name, _symbol, _payload, mode));
        lastDigest = digest;
        totalScore += (uint256(digest) & 0xffffffff) + combinedLen;
        emit StorageBytesObserved(totalScore, lastDigest, combinedLen);
        return totalScore;
    }

    function getName() external view returns (string memory) {
        return _name;
    }

    function getPayload() external view returns (bytes memory) {
        return _payload;
    }

    function fail() external {
        _name = "reverted-long-string-that-allocates-keccak-storage-slots-0123456789";
        totalScore += 999;
        bytes32 d = keccak256(bytes(_name));
        uint256 errLen = bytes(_name).length;
        revert StorageBytesBlocked(999, d, errLen);
    }

    function read() external view returns (uint256, bytes32, uint256) {
        uint256 lenMetric = bytes(_name).length + bytes(_symbol).length + _payload.length + syncCount;
        return (totalScore, lastDigest, lenMetric);
    }
}
