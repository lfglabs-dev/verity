// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Neutral calldata-slice batch dispatcher smoke: a root `bytes[] calldata`
// parameter, a loop over the items, a 4-byte selector extracted with
// `bytes4(items[i][:4])` or `bytes calldata item = items[i]; bytes4(item[:4])`,
// argument slices decoded with `abi.decode(item[4:], (...))` or a slice local
// `bytes calldata payload = item[4:]`, `if` / `else if` dispatch to internal
// calls of the handlers, and a revert on unknown selectors.

contract CalldataSliceDispatchSmoke {
    event Handled(bytes4 indexed selector, uint256 value);

    uint256 public total;
    address public lastWho;

    function addPair(uint256 a, uint256 b) public returns (uint256) {
        total += a + b;
        uint256 pairSum = a + b;
        emit Handled(this.addPair.selector, pairSum);
        return pairSum;
    }

    function touchOne(address who, uint256 amount) public returns (uint256) {
        total += amount;
        lastWho = who;
        emit Handled(this.touchOne.selector, amount);
        return amount;
    }

    function scaleOne(uint256 x, uint32 factor) public pure returns (uint256) {
        return x * factor;
    }

    function batch(bytes[] calldata items) external returns (uint256 sum) {
        uint256 n = items.length;
        for (uint256 i = 0; i < n; i++) {
            require(items[i].length >= 4, "short");
            bytes4 selector = bytes4(items[i][:4]);
            if (selector == this.addPair.selector) {
                (uint256 a, uint256 b) = abi.decode(items[i][4:], (uint256, uint256));
                sum += addPair(a, b);
            } else if (selector == this.touchOne.selector) {
                (address who, uint256 amount) = abi.decode(items[i][4:], (address, uint256));
                sum += touchOne(who, amount);
            } else if (selector == this.scaleOne.selector) {
                (uint256 x, uint32 factor) = abi.decode(items[i][4:], (uint256, uint32));
                sum += scaleOne(x, factor);
            } else {
                revert("unknown selector");
            }
        }
        return sum;
    }

    function batchLocal(bytes[] calldata items) external returns (uint256 sum) {
        uint256 n = items.length;
        for (uint256 i = 0; i < n; i++) {
            bytes calldata item = items[i];
            require(item.length >= 4, "short");
            bytes4 selector = bytes4(item[:4]);
            if (selector == this.addPair.selector) {
                bytes calldata payload = item[4:];
                (uint256 a, uint256 b) = abi.decode(payload, (uint256, uint256));
                sum += addPair(a, b);
            } else if (selector == this.touchOne.selector) {
                (address who, uint256 amount) = abi.decode(item[4:], (address, uint256));
                sum += touchOne(who, amount);
            } else if (selector == this.scaleOne.selector) {
                (uint256 x, uint32 factor) = abi.decode(item[4:], (uint256, uint32));
                sum += scaleOne(x, factor);
            } else {
                revert("unknown selector");
            }
        }
        return sum;
    }

    function batchDirectDecode(bytes[] calldata items) external returns (uint256 sum) {
        for (uint256 i = 0; i < items.length; i++) {
            (uint256 a, uint256 b) = abi.decode(items[i], (uint256, uint256));
            sum += addPair(a, b);
        }
        return sum;
    }
}

contract CalldataSliceDispatchUnsupported {
    function reassignLocal(bytes[] calldata items) external pure returns (uint256) {
        bytes calldata item = items[0];
        item = items[1];
        return item.length;
    }
}
