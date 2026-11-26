// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

// Minimal synthetic paginated linked-list shrink + near-miss rejection cases (Refs #2620).
contract YulArrayLengthShrink {
    address internal constant HEAD = address(0x1);
    mapping(address => address) private links;

    function paginate(address start, uint256 pageSize)
        external
        view
        returns (address[] memory page, address next)
    {
        require(pageSize > 0, "zero page");
        page = new address[](pageSize);
        uint256 count = 0;
        next = links[start];
        while (next != address(0) && next != HEAD && count < pageSize) {
            page[count] = next;
            next = links[next];
            count++;
        }
        if (next != HEAD) {
            next = page[count - 1];
        }
        assembly {
            mstore(page, count)
        }
    }

    function growLiteral() external pure returns (uint256[] memory xs) {
        xs = new uint256[](3);
        assembly {
            mstore(xs, 5)
        }
    }

    function growInclusiveLoop(uint256 cap) external pure returns (uint256[] memory xs) {
        xs = new uint256[](cap);
        uint256 count = 0;
        while (count <= cap) {
            count++;
        }
        assembly {
            mstore(xs, count)
        }
    }

    function nonArrayScalar() external pure returns (uint256 p) {
        p = 0x80;
        assembly {
            mstore(p, 0)
        }
    }

    function nonArrayBytes() external pure returns (bytes memory b) {
        b = abi.encode(uint256(1));
        assembly {
            mstore(b, 0)
        }
    }

    function nonArrayFixed() external pure returns (uint256) {
        uint256[2] memory fixedArr;
        assembly {
            mstore(fixedArr, 1)
        }
        return fixedArr[0];
    }

    function offsetTarget() external pure returns (uint256[] memory xs) {
        xs = new uint256[](3);
        assembly {
            mstore(add(xs, 0x20), 0)
        }
    }

    function unprovedLenParam(uint256 cap, uint256 n) external pure returns (uint256[] memory xs) {
        xs = new uint256[](cap);
        assembly {
            mstore(xs, n)
        }
    }

    function unprovedShortCircuitInit(bool keepGoing, uint256 cap)
        external
        pure
        returns (uint256[] memory xs)
    {
        xs = new uint256[](cap);
        uint256 count = 5;
        while (keepGoing && count < cap) {
            count++;
        }
        assembly {
            mstore(xs, count)
        }
    }

    function parameterArrayTarget(uint256[] memory xs) external pure returns (uint256) {
        assembly {
            mstore(xs, 0)
        }
        return xs.length;
    }

    function aliasedArrayTarget() external pure returns (uint256) {
        uint256[] memory xs = new uint256[](3);
        uint256[] memory aliasView;
        aliasView = xs;
        assembly {
            mstore(xs, 1)
        }
        return aliasView.length;
    }
}
