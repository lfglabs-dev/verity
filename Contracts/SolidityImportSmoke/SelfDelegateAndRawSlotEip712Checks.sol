// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Neutral synthetic fixture exercising:
/// 4A. Generic `address(this).delegatecall(...)` self-dispatch (batch multicall & single call),
///     plus fail-closed controls for external `target.delegatecall` and `{gas: ...}` options.
/// 4B. `bytes` / `bytes[]` written-type matching in `solidity_import` root signatures.
/// 4C. Raw-slot (ERC-7201 style) struct with `string` and cached EIP-712 domain separator.
contract SelfDelegateAndRawSlotEip712Fixture {
    bytes32 private constant DOMAIN_STORAGE_SLOT =
        0x111122223333444455556666777788889999aaaabbbbccccddddeeeeffff0000;
    bytes32 private constant DOMAIN_TYPEHASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");
    bytes32 private constant PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    struct DomainStorage {
        bytes32 cachedDomainSeparator;
        uint256 cachedChainId;
        string name;
        string version;
    }

    mapping(address => uint256) public nonces;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public counter;

    function _getDomainStorage() private pure returns (DomainStorage storage $) {
        assembly {
            $.slot := DOMAIN_STORAGE_SLOT
        }
    }

    function _buildDomainSeparator(DomainStorage storage $) private view returns (bytes32) {
        return keccak256(
            abi.encode(
                DOMAIN_TYPEHASH,
                keccak256(bytes($.name)),
                keccak256(bytes($.version)),
                block.chainid,
                address(this)
            )
        );
    }

    function initDomain(string calldata name_, string calldata version_) external returns (bytes32) {
        DomainStorage storage $ = _getDomainStorage();
        $.name = name_;
        $.version = version_;
        $.cachedChainId = block.chainid;
        bytes32 sep = _buildDomainSeparator($);
        $.cachedDomainSeparator = sep;
        return sep;
    }

    function domainSeparator() public view returns (bytes32) {
        DomainStorage storage $ = _getDomainStorage();
        if (block.chainid == $.cachedChainId && $.cachedDomainSeparator != bytes32(0)) {
            return $.cachedDomainSeparator;
        }
        return _buildDomainSeparator($);
    }

    function permitWithBytes(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        bytes calldata sig
    ) external returns (bytes32) {
        require(deadline >= block.timestamp, "EXPIRED");
        require(sig.length == 65, "BAD_SIG_LEN");
        uint256 nonce = nonces[owner];
        bytes32 structHash = keccak256(
            abi.encode(PERMIT_TYPEHASH, owner, spender, value, nonce, deadline)
        );
        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator(), structHash));
        nonces[owner] = nonce + 1;
        allowance[owner][spender] = value;
        return digest;
    }

    function multicall(bytes[] calldata data) external returns (uint256 executed) {
        for (uint256 i = 0; i < data.length; i++) {
            (bool success, bytes memory result) = address(this).delegatecall(data[i]);
            if (!success) {
                assembly {
                    revert(add(result, 0x20), mload(result))
                }
            }
            executed += 1;
        }
    }

    function selfDispatchSingle(bytes calldata payload) external returns (bytes memory) {
        (bool success, bytes memory result) = address(this).delegatecall(payload);
        if (!success) {
            assembly {
                revert(add(result, 0x20), mload(result))
            }
        }
        return result;
    }

    // Fail-closed control: external `target.delegatecall` must stay rejected.
    function externalDelegateRejected(address target, bytes calldata payload) external returns (bool) {
        (bool success, ) = target.delegatecall(payload);
        return success;
    }

    // Fail-closed control: `address(this).delegatecall{gas: ...}` must stay rejected.
    function gassedSelfDelegateRejected(bytes calldata payload) external returns (bool) {
        (bool success, ) = address(this).delegatecall{gas: 50000}(payload);
        return success;
    }

    // Fail-closed control: storage write after self-delegatecall violates CEI.
    function multicallPostWriteRejected(bytes[] calldata data) external returns (uint256 executed) {
        for (uint256 i = 0; i < data.length; i++) {
            (bool success, bytes memory result) = address(this).delegatecall(data[i]);
            if (!success) {
                assembly {
                    revert(add(result, 0x20), mload(result))
                }
            }
            executed += 1;
        }
        counter += executed;
    }

    // Fail-closed control: payable self-delegatecall reuses msg.value across sub-calls and
    // imported roots compile as nonpayable.
    function payableMulticallRejected(bytes[] calldata data) external payable returns (uint256 executed) {
        for (uint256 i = 0; i < data.length; i++) {
            (bool success, bytes memory result) = address(this).delegatecall(data[i]);
            if (!success) {
                assembly {
                    revert(add(result, 0x20), mload(result))
                }
            }
            executed += 1;
        }
    }
}
