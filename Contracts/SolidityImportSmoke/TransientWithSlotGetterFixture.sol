// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// Clean-room fixture for R9: EIP-7201 constant-slot storage-pointer getter
/// (`assembly { $.slot := STORE_SLOT }` and literal `assembly { $.slot := 0x1111...1100 }`)
/// combined with a `transient bool` state variable, plus negative controls ensuring
/// arbitrary or dynamic-slot inline assembly in transient closures remains rejected.
contract TransientWithSlotGetterFixture {
    struct Store {
        uint256 value;
        uint256 batchRuns;
        mapping(address => uint256) credits;
    }

    bytes32 private constant STORE_SLOT =
        0x1111111111111111111111111111111111111111111111111111111111111100;

    bool private transient _inBatch;

    function _getStore() private pure returns (Store storage $) {
        assembly {
            $.slot := STORE_SLOT
        }
    }

    function _getStoreLiteral() private pure returns (Store storage $) {
        assembly ("memory-safe") {
            $.slot := 0x1111111111111111111111111111111111111111111111111111111111111100
        }
    }

    function _getStoreDynamic(bytes32 slot) private pure returns (Store storage $) {
        assembly {
            $.slot := slot
        }
    }

    function _getStoreWithExtraAsm() private view returns (Store storage $) {
        assembly {
            $.slot := STORE_SLOT
        }
        uint256 junk;
        assembly {
            junk := tload(0)
        }
        if (junk == type(uint256).max) {
            revert();
        }
    }

    function _addValue(uint256 delta, address account) internal returns (uint256) {
        Store storage $ = _getStore();
        if (!_inBatch) {
            $.value += delta;
        } else {
            $.value += delta * 2;
            $.batchRuns += 1;
        }
        $.credits[account] += delta;
        return $.value;
    }

    function addDirect(uint256 delta, address account) external returns (uint256) {
        return _addValue(delta, account);
    }

    function addInBatch(uint256 a, uint256 b, address account) external returns (uint256) {
        require(!_inBatch, "reentrant batch");
        _inBatch = true;
        uint256 first = _addValue(a, account);
        Store storage $lit = _getStoreLiteral();
        $lit.value += b;
        uint256 total = $lit.value;
        _inBatch = false;
        return first + total;
    }

    function addInBatchRevert(uint256 delta, address account) external {
        _inBatch = true;
        _addValue(delta, account);
        require(false, "rollback");
    }

    function readState(address account)
        external
        view
        returns (uint256 value, uint256 batchRuns, uint256 credit, bool inBatch)
    {
        Store storage $ = _getStore();
        return ($.value, $.batchRuns, $.credits[account], _inBatch);
    }

    // Negative control 1: arbitrary tload assembly in a transient closure
    function badArbitraryAsm() external returns (uint256 word) {
        _inBatch = true;
        Store storage $ = _getStore();
        $.value += 1;
        assembly {
            word := tload(0)
        }
    }

    // Negative control 2: dynamic/parameter slot binding in a transient closure
    function badDynamicSlotAsm(bytes32 slot) external returns (uint256) {
        _inBatch = true;
        Store storage $ = _getStoreDynamic(slot);
        $.value += 1;
        return $.value;
    }

    // Negative control 3: multi-statement assembly in a storage-pointer getter in a transient closure
    function badExtraAsmInGetter() external returns (uint256) {
        _inBatch = true;
        Store storage $ = _getStoreWithExtraAsm();
        $.value += 1;
        return $.value;
    }
}
