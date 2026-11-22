// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface IAbiEncodeUdvtTarget {
    function accept(bytes32 word, uint48 tag, address holder) external;
}

type WordId is bytes32;
type NarrowTag is uint48;
type Holder is address;

// `T.unwrap(x)` / `T.wrap(x)` on user-defined value types as `abi.encode*` arguments: the
// identity on the underlying word, including a narrow (`uint48`) packed width and a
// library helper that derives a mapping-style slot from an unwrapped id.
library WordIdSlots {
    bytes32 internal constant BASE_SLOT = bytes32(uint256(6));

    function slotOf(WordId id) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(WordId.unwrap(id), BASE_SLOT));
    }
}

contract SequenceFixture {
    uint256 internal saved;

    function _current() internal view returns (WordId) {
        return WordId.wrap(bytes32(saved));
    }

    function change(uint256 next) external returns (uint256) {
        WordId id = WordId.wrap(bytes32(next));
        NarrowTag tag = NarrowTag.wrap(uint48(next >> 3));
        bytes32 digest;
        if (next % 4 == 0) {
            digest = WordIdSlots.slotOf(id);
        } else if (next % 4 == 1) {
            digest = keccak256(abi.encode(
                WordId.unwrap(_current()),
                NarrowTag.unwrap(NarrowTag.wrap(uint48(next))),
                Holder.unwrap(Holder.wrap(msg.sender))));
        } else if (next % 4 == 2) {
            digest = keccak256(abi.encodePacked(
                NarrowTag.unwrap(tag),
                WordId.unwrap(WordId.wrap(keccak256(abi.encode(next)))),
                NarrowTag.unwrap(tag),
                NarrowTag.wrap(uint48(next)),
                tag));
        } else {
            digest = keccak256(abi.encodeWithSelector(
                IAbiEncodeUdvtTarget.accept.selector,
                WordId.unwrap(id),
                NarrowTag.unwrap(tag),
                Holder.unwrap(Holder.wrap(address(this))),
                WordId.wrap(bytes32(next >> 1))));
        }
        saved = uint256(digest);
        return saved;
    }

    function fail() external {
        saved = 77;
        revert();
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
