// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IEndpoint {
    function quote(uint256 amount, bytes32 tag) external view returns (uint256);
    function notify(uint256 amount, bytes32 tag) external;
    function dispatch(address to, uint256 amount, bytes calldata data) external;
}

/// Synthetic fixture covering:
/// - `abi.encodeWithSelector` with dynamic `bytes memory` / `bytes calldata` arguments
///   (standalone and mixed with static head args).
/// - Named arguments on ordinary typed external calls and external `try` calls
///   (both declared order and reordered, void and value-returning, static and dynamic args).
/// - `new bytes(0)` empty bytes allocation and `enum` fields inside `Struct[]`
///   ABI schemas (`calldata`, `memory`, nested inside dynamic struct, local `new Struct[](n)`).
contract DynamicSelectorNamedTryEnumArray {
    enum ActionKind {
        Deposit,
        Withdraw,
        Rebalance
    }

    struct ActionItem {
        ActionKind kind;
        address asset;
        uint128 amount;
        bool active;
    }

    struct ActionBatch {
        ActionItem[] items;
        bytes note;
    }

    uint256 internal lastCount;

    // abi.encodeWithSelector with dynamic bytes memory / calldata
    function hashSelectorDynMem(bytes4 sel, bytes memory payload)
        external
        pure
        returns (bytes32)
    {
        return keccak256(abi.encodeWithSelector(sel, payload));
    }

    function hashSelectorDynCalldata(bytes4 sel, bytes calldata payload)
        external
        pure
        returns (bytes32)
    {
        return keccak256(abi.encodeWithSelector(sel, payload));
    }

    function hashSelectorMixed(
        bytes4 sel,
        address to,
        uint256 amount,
        bool flag,
        bytes memory payload
    ) external pure returns (bytes32) {
        return keccak256(abi.encodeWithSelector(sel, to, amount, flag, payload));
    }

    function hashSelectorTwoDyn(
        bytes4 sel,
        address to,
        bytes calldata headData,
        uint256 amount,
        bytes memory tailData
    ) external pure returns (bytes32) {
        return keccak256(abi.encodeWithSelector(sel, to, headData, amount, tailData));
    }

    // Named arguments on ordinary typed external calls & external try calls
    function namedExternalQuote(IEndpoint ep, uint256 x, bytes32 tag)
        external
        view
        returns (uint256)
    {
        uint256 a = ep.quote({amount: x, tag: tag});
        uint256 b = ep.quote({tag: tag, amount: x + 1});
        return a + b;
    }

    function namedExternalDispatch(IEndpoint ep, address to, uint256 x, bytes memory data)
        external
    {
        ep.dispatch({data: data, amount: x, to: to});
    }

    function namedTryVoid(IEndpoint ep, uint256 x, bytes32 tag) external returns (uint256) {
        try ep.notify({tag: tag, amount: x}) {
            lastCount += 1;
            return 1;
        } catch {
            return 0;
        }
    }

    function namedTryReturn(IEndpoint ep, uint256 x, bytes32 tag)
        external
        view
        returns (uint256)
    {
        try ep.quote({tag: tag, amount: x}) returns (uint256 out) {
            return out + 7;
        } catch {
            return 999;
        }
    }

    // new bytes(0) empty bytes allocation
    function emptyBytesChecks(bytes4 sel, uint256 x)
        external
        pure
        returns (bytes32 hEmpty, bytes32 hEnc, bytes32 hSel, uint256 len)
    {
        bytes memory empty = new bytes(0);
        hEmpty = keccak256(new bytes(0));
        hEnc = keccak256(abi.encode(x, new bytes(0)));
        hSel = keccak256(abi.encodeWithSelector(sel, new bytes(0)));
        len = empty.length;
    }

    function callWithNewEmptyBytes(address target, uint256 value) external returns (bool) {
        (bool success,) = target.call{value: value}(new bytes(0));
        return success;
    }

    // Enum fields inside Struct[] ABI schemas (calldata, memory, nested, local array)
    function sumCalldataEnumItems(ActionItem[] calldata items)
        external
        pure
        returns (uint256 total, uint256 kindSum)
    {
        for (uint256 i = 0; i < items.length; ++i) {
            ActionItem memory item = items[i];
            if (item.active) {
                total += item.amount;
                kindSum += uint256(uint8(item.kind));
            }
        }
    }

    function sumMemoryEnumItems(ActionItem[] memory items)
        external
        pure
        returns (uint256 total, uint256 kindSum)
    {
        for (uint256 i = 0; i < items.length; ++i) {
            if (items[i].active) {
                total += items[i].amount;
                kindSum += uint256(uint8(items[i].kind));
            }
        }
    }

    function sumBatchEnumItems(ActionBatch calldata batch)
        external
        pure
        returns (uint256 total, uint256 noteLen)
    {
        for (uint256 i = 0; i < batch.items.length; ++i) {
            total += uint256(uint8(batch.items[i].kind)) * 100 + batch.items[i].amount;
        }
        noteLen = batch.note.length;
    }

    function buildLocalEnumStructArray(address asset, uint128 amt)
        external
        pure
        returns (uint256)
    {
        ActionItem[] memory arr = new ActionItem[](2);
        arr[0] = ActionItem({
            kind: ActionKind.Deposit,
            asset: asset,
            amount: amt,
            active: true
        });
        arr[1] = ActionItem({
            kind: ActionKind.Rebalance,
            asset: asset,
            amount: amt + 5,
            active: true
        });
        return uint256(uint8(arr[0].kind)) + uint256(uint8(arr[1].kind)) * 10 + arr[1].amount;
    }
}
