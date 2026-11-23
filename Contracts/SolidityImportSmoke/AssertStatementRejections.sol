// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract VoidConditionalC {
    uint256 internal a;
    uint256 internal b;

    function left() internal { a += 1; }

    function right() internal { b += 1; }

    function run(uint256 x) external {
        x > 0 ? left() : right();
    }
}

contract StructConstructorC {
    struct Pair {
        uint256 a;
        uint256 b;
    }

    function run(uint256 x) external pure {
        Pair(x, 1);
    }
}

contract InlineArrayC {
    function run(uint256 x) external pure {
        [x, 1];
    }
}

contract TupleC {
    function run(uint256 x) external pure {
        (x, 1);
    }
}

contract TypeNameC {
    function run(uint256) external pure {
        uint256;
    }
}
