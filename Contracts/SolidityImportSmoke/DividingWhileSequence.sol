// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

/// `while` loops whose only progress is dividing an unsigned local by a constant: against a
/// constant (`v > LIMIT`), against a local the body does not change (`bound < v`), and against
/// zero through a narrow cast (`v != 0`, `v = v / 3`). The first loop's body can revert, and
/// one input runs it 73 times.
contract SequenceFixture {
    uint256 private constant LIMIT = 4095;

    uint256 private packed;
    uint256 private steps;

    error NotDivisible(uint256 value);

    function change(uint256 x) external returns (uint256) {
        uint256 reduced = x;
        uint256 dropped = 0;
        while (reduced > LIMIT) {
            require(reduced % 10 == 0, NotDivisible(reduced));
            reduced /= 10;
            dropped++;
        }
        uint256 halved = x;
        uint256 bound = 1000;
        uint256 halvings = 0;
        while (bound < halved) {
            halvings += 1;
            halved = halved / 2;
        }
        uint24 small = uint24(x);
        uint256 thirds = 0;
        while (small != 0) {
            small = small / 3;
            thirds += 1;
        }
        packed = reduced + dropped * 10000;
        steps = halvings * 1000 + thirds;
        return packed;
    }

    function fail() external view {
        require(steps <= 15, "range");
    }

    function read() external view returns (uint256) {
        return packed + steps * 2;
    }
}
