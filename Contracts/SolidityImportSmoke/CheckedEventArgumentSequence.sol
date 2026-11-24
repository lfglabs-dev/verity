// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Checked arithmetic as event arguments. Each argument is evaluated with its overflow
// check before the log is written, so an overflow reverts with Panic(0x11), logs
// nothing (not even an earlier event of the same call) and rolls back the storage
// writes before it. Unsigned and signed sums, differences and products, at full and
// narrow widths, indexed and not, positional and named in declaration order.
contract SequenceFixture {
    event Synced(uint256 indexed id, uint256 sum, uint256 difference);
    event Narrow(uint64 indexed sum, int104 signedSum, int256 signedDifference);
    event Scaled(uint128 product, int64 signedProduct);

    uint256 private total;
    uint256 private paid;
    uint64 private small;
    int104 private delta;

    function change(uint256 next) external returns (uint256) {
        uint256 mode = next % 4;
        if (mode == 0) {
            uint256 prior = total;
            total = next;
            emit Synced({id: next, sum: prior + next, difference: next - paid});
        } else if (mode == 1) {
            uint64 low = uint64(next >> 8);
            small = low;
            emit Narrow(low + uint64(next >> 192), delta + int104(int256(next >> 152)),
                int256(next) - int256(paid));
        } else if (mode == 2) {
            delta = int104(int256(next));
            emit Scaled(uint128(next >> 4) * uint128(next >> 196),
                int64(int256(next >> 8)) * int64(delta));
        } else {
            paid = next >> 2;
            emit Synced(next, next, 0);
            emit Synced(next, total + next, total - paid);
        }
        return total;
    }

    function read() external view returns (uint256) {
        return total ^ paid ^ small ^ uint256(int256(delta));
    }
}
