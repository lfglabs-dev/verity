// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Direct calls of `public` and `external` library functions, which solc lowers to a
// DELEGATECALL into the linked library (#2728). Imported with
// `linkedLibrariesMatchSource := true`, the model inlines the library bodies; the source
// route deploys both libraries and links them into the contract. The packing call is an
// external library function whose packed `(uint256(options) << 160) | uint160(pointer)` word
// is written to a mapping entry.

enum CallOptions {
    None,
    Send,
    DelegateCall,
    Both
}

library LinkedPackLib {
    event Packed(address indexed caller, uint256 word);

    function pack(address pointer, CallOptions options) external pure returns (uint256) {
        return (uint256(options) << 160) | uint160(pointer);
    }

    function packLogged(address pointer, CallOptions options) public returns (uint256 word) {
        word = (uint256(options) << 160) | uint160(pointer);
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
        return total + LinkedPackLib.pack(pointer, CallOptions.Send);
    }
}

contract LinkedLibraryCallFixture {
    mapping(bytes32 => uint256) internal scopeConfig;
    mapping(bytes32 => LinkedCounterLib.Counter) internal counters;
    LinkedCounterLib.Counter internal main;
    uint256 internal lastWord;

    function setScope(bytes32 key, address pointer, CallOptions options) external {
        scopeConfig[key] = LinkedPackLib.pack(pointer, options);
    }

    function setScopeLogged(bytes32 key, address pointer, CallOptions options) external {
        scopeConfig[key] = LinkedPackLib.packLogged(pointer, options);
    }

    function scope(bytes32 key) external view returns (uint256) {
        return scopeConfig[key];
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
