// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// OpenZeppelin Contracts (last updated v5.3.0) (proxy/utils/Initializable.sol), code quoted
// as is; NatSpec comments are dropped. The `initializer` guard admits a second call while
// the executing account has no code: `address(this).code.length == 0` holds while a proxy's
// constructor delegatecalls `initialize`, and never once the account has runtime code.
abstract contract Initializable {
    /// @custom:storage-location erc7201:openzeppelin.storage.Initializable
    struct InitializableStorage {
        uint64 _initialized;
        bool _initializing;
    }

    // keccak256(abi.encode(uint256(keccak256("openzeppelin.storage.Initializable")) - 1)) & ~bytes32(uint256(0xff))
    bytes32 private constant INITIALIZABLE_STORAGE = 0xf0c57e16840df040f15088dc2f81fe391c3923bec73e23a9662efc9c229c6a00;

    error InvalidInitialization();

    error NotInitializing();

    event Initialized(uint64 version);

    modifier initializer() {
        // solhint-disable-next-line var-name-mixedcase
        InitializableStorage storage $ = _getInitializableStorage();

        // Cache values to avoid duplicated sloads
        bool isTopLevelCall = !$._initializing;
        uint64 initialized = $._initialized;

        // Allowed calls:
        // - initialSetup: the contract is not in the initializing state and no previous version was
        //                 initialized
        // - construction: the contract is initialized at version 1 (no reinitialization) and the
        //                 current contract is just being deployed
        bool initialSetup = initialized == 0 && isTopLevelCall;
        bool construction = initialized == 1 && address(this).code.length == 0;

        if (!initialSetup && !construction) {
            revert InvalidInitialization();
        }
        $._initialized = 1;
        if (isTopLevelCall) {
            $._initializing = true;
        }
        _;
        if (isTopLevelCall) {
            $._initializing = false;
            emit Initialized(1);
        }
    }

    modifier onlyInitializing() {
        _checkInitializing();
        _;
    }

    function _checkInitializing() internal view virtual {
        if (!_isInitializing()) {
            revert NotInitializing();
        }
    }

    function _getInitializedVersion() internal view returns (uint64) {
        return _getInitializableStorage()._initialized;
    }

    function _isInitializing() internal view returns (bool) {
        return _getInitializableStorage()._initializing;
    }

    function _initializableStorageSlot() internal pure virtual returns (bytes32) {
        return INITIALIZABLE_STORAGE;
    }

    // solhint-disable-next-line var-name-mixedcase
    function _getInitializableStorage() private pure returns (InitializableStorage storage $) {
        bytes32 slot = _initializableStorageSlot();
        assembly {
            $.slot := slot
        }
    }
}

// Every admitted orientation of a zero test on the executing account's code length.
contract SelfCodeLengthFixture is Initializable {
    error NoCode();

    uint256 private value;
    uint256 private marks;

    function initialize(uint256 initial) external initializer {
        __SelfCodeLength_init(initial);
    }

    function __SelfCodeLength_init(uint256 initial) internal onlyInitializing {
        value = initial;
    }

    function hasCode() external view returns (bool) {
        return address(this).code.length != 0;
    }

    function noCode() external view returns (bool) {
        return address(this).code.length == 0;
    }

    function orientations() external view returns (bool, bool, bool, bool) {
        return (0 == address(this).code.length, 0 != address(this).code.length,
            address(this).code.length > 0, 0 < address(this).code.length);
    }

    function mark(uint256 amount) external {
        if (address(this).code.length > 0) {
            marks += amount;
        } else {
            marks += 2 * amount;
        }
    }

    function requireCode() external view returns (uint256) {
        require(address(this).code.length != 0, NoCode());
        return value;
    }

    function state() external view returns (uint64, bool, uint256, uint256) {
        return (_getInitializedVersion(), _isInitializing(), value, marks);
    }
}
