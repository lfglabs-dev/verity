// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// `assert(c)` and expression statements whose value is discarded. Both solc 0.8.34
// pipelines evaluate the assert condition once and revert with `Panic(0x01)` when it is
// false; a discarded expression is still evaluated, so its checks keep their panics
// (`10 / y;` is `Panic(0x12)` at y = 0, `arr[y];` `Panic(0x32)`, `y - 1;` `Panic(0x11)`,
// `Mode(y);` `Panic(0x21)`) and its calls their effects. change(x) selects case x % 8
// and drives it with y = x / 8.
contract SequenceFixture {
    enum Mode {
        Off,
        On,
        Auto
    }

    uint256 internal count;
    uint256 internal stamp;
    uint256[] internal arr;

    event Seen(uint256 selector, uint256 count, uint256 stamp);

    // State-changing assert condition: true unless the new count is a multiple of 3.
    function step() internal returns (bool) {
        count += 1;
        return count % 3 != 0;
    }

    function check(uint256 v) internal pure {
        assert(v != 13);
    }

    function change(uint256 x) external returns (uint256) {
        uint256 c = x % 8;
        uint256 y = x / 8;
        stamp = x;
        if (arr.length == 0) {
            arr.push();
            arr.push();
        }
        // Holds unless y = 1.
        if (c == 0) { assert(y != 1); }
        // The condition's write happens once, and is rolled back when it fails.
        if (c == 1) { assert(step()); }
        // A panicking condition reverts with its own panic, not 0x01 (y = 0: 0x12; y = 3: 0x01).
        if (c == 2) { assert(10 / y != 3); }
        // Effect-free discarded values; `y - 1` still panics at y = 0.
        if (c == 3) {
            y;
            this;
            7;
            stamp;
            (y);
            -int256(y);
            uint8(y);
            arr.length;
            y - 1;
        }
        // Reverting discarded values.
        if (c == 4) { 10 / y; }
        if (c == 5) { arr[y]; }
        // A discarded value with an effect, a discarded enum conversion (y >= 3: 0x21),
        // and an unchecked discarded value (no panic).
        if (c == 6) {
            !step();
            unchecked { y - 1; }
            Mode(y);
        }
        // assert in an inlined helper (y = 13).
        if (c == 7) { check(y); }
        emit Seen(c, count, stamp);
        return count;
    }

    function fail() external {
        stamp = 123;
        assert(false);
    }

    function read() external view returns (uint256) {
        return count * 1000 + stamp % 1000 + arr.length;
    }
}
