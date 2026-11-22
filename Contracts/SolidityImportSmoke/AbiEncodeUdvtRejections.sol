// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

type WordId is bytes32;
type PackedTag is uint48;

// An effect beneath `T.unwrap(...)` in an `abi.encode*` argument stays a located rejection, except a state-changing helper in plain `abi.encode` (`UnwrapStatefulC`, evaluated in order).
contract UnwrapRevertC {
    error Blocked();

    function _mayRevert(uint256 x) internal pure returns (WordId) {
        if (x == 0) revert Blocked();
        return WordId.wrap(bytes32(x));
    }

    function digest(uint256 x) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(WordId.unwrap(_mayRevert(x)), x));
    }
}

contract UnwrapStatefulC {
    uint256 internal nonce;

    function _useWord() internal returns (WordId) {
        return WordId.wrap(bytes32(nonce++));
    }

    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encode(x, WordId.unwrap(_useWord())));
    }
}

contract WrapStatefulC {
    uint256 internal nonce;

    function _useCount() internal returns (uint48) {
        return uint48(nonce++);
    }

    function digest(uint256 x) external returns (bytes32) {
        return keccak256(abi.encodePacked(x, PackedTag.wrap(_useCount())));
    }
}
