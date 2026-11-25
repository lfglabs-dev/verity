// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Direct calls of `public` and `external` library functions, which solc lowers to a
// DELEGATECALL into the linked library (#2728). Imported with
// `linkedLibrariesMatchSource := true`, the model inlines the library bodies; the source
// route deploys both libraries and links them into the contract. The packing call is an
// external library function whose packed `(uint256(mode) << 160) | uint160(pointer)` word
// is written to a mapping entry.

enum Mode {
    A,
    B,
    C,
    D
}

library LinkedPackLib {
    event Packed(address indexed caller, uint256 word);

    function pack(address pointer, Mode mode) external pure returns (uint256) {
        return (uint256(mode) << 160) | uint160(pointer);
    }

    function packLogged(address pointer, Mode mode) public returns (uint256 word) {
        word = (uint256(mode) << 160) | uint160(pointer);
        emit Packed(msg.sender, word);
    }
}

library LinkedCounterLib {
    struct Counter {
        uint256 total;
        address last;
        uint64 calls;
    }

    error ValueTooLarge(uint256 value);

    event Bumped(address indexed caller, address indexed self, uint256 total);

    function bump(Counter storage c, uint256 amount) public returns (uint256) {
        if (amount > 0x8000000000000000000000000000000000000000000000000000000000000000) {
            revert ValueTooLarge(amount);
        }
        require(amount != 7, "seven");
        c.total += amount;
        c.last = msg.sender;
        c.calls += 1;
        emit Bumped(msg.sender, address(this), c.total);
        return c.total;
    }

    function reset(Counter storage c) public {
        c.total = 0;
        c.calls = 0;
    }

    function share(Counter storage c, uint256 parts) external view returns (uint256) {
        return c.total / parts;
    }

    function bumpPacked(Counter storage c, uint256 amount, address pointer)
        external
        returns (uint256)
    {
        uint256 total = bump(c, amount);
        return total + LinkedPackLib.pack(pointer, Mode.B);
    }
}

contract LinkedLibraryCallFixture {
    mapping(bytes32 => uint256) internal packedWords;
    mapping(bytes32 => LinkedCounterLib.Counter) internal counters;
    LinkedCounterLib.Counter internal main;
    uint256 internal lastWord;

    function setConfig(bytes32 key, address pointer, Mode mode) external {
        packedWords[key] = LinkedPackLib.pack(pointer, mode);
    }

    function setConfigLogged(bytes32 key, address pointer, Mode mode) external {
        packedWords[key] = LinkedPackLib.packLogged(pointer, mode);
    }

    function word(bytes32 key) external view returns (uint256) {
        return packedWords[key];
    }

    function bump(bytes32 key, uint256 amount) external returns (uint256) {
        return LinkedCounterLib.bump(counters[key], amount);
    }

    function bumpMain(uint256 amount) external {
        uint256 bumped = LinkedCounterLib.bump(main, amount);
        lastWord = bumped + 1;
    }

    function bumpPacked(bytes32 key, uint256 amount, address pointer) external returns (uint256) {
        return LinkedCounterLib.bumpPacked(counters[key], amount, pointer);
    }

    function reset(bytes32 key) external {
        LinkedCounterLib.reset(counters[key]);
    }

    function share(bytes32 key, uint256 parts) external view returns (uint256) {
        return LinkedCounterLib.share(counters[key], parts);
    }

    function total(bytes32 key) external view returns (uint256) {
        return counters[key].total;
    }

    function last(bytes32 key) external view returns (address) {
        return counters[key].last;
    }

    function calls(bytes32 key) external view returns (uint64) {
        return counters[key].calls;
    }

    function mainState() external view returns (uint256, uint256) {
        return (main.total, lastWord);
    }
}
