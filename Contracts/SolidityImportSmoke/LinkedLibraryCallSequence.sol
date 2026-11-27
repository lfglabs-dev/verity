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

type Narrow8 is uint8;

library WideShadowLib {
    type Narrow8 is uint256;
}

library LinkedPackLib {
    error BadPayload(uint256 length, bytes1 firstByte);

    event Packed(address indexed caller, uint256 word);

    function pack(address pointer, Mode mode) external pure returns (uint256) {
        return (uint256(mode) << 160) | uint160(pointer);
    }

    function packLogged(address pointer, Mode mode) public returns (uint256 word) {
        word = (uint256(mode) << 160) | uint160(pointer);
        emit Packed(msg.sender, word);
    }

    function passUint8(uint8 v) external pure returns (uint8) {
        return v;
    }

    function roundTripNarrow(
        uint8 u,
        int8 s,
        bool flag,
        Narrow8 wrapped,
        address addr,
        bytes4 sel
    ) external pure returns (uint8, int8, bool, Narrow8, address, bytes4) {
        return (u, s, flag, wrapped, addr, sel);
    }

    function narrowSingleFromWide(uint256 raw) external pure returns (uint8) {
        return uint8(raw);
    }

    function narrowMultiFromWide(uint256 rawAddr, bytes32 rawSel)
        external
        pure
        returns (address, bytes4)
    {
        return (address(uint160(rawAddr)), bytes4(rawSel));
    }

    function mutateAndTag(bytes memory payload, bytes1 replacement, uint8 suffix)
        external
        pure
        returns (bytes memory out)
    {
        bytes memory buf = new bytes(payload.length + 1);
        for (uint256 i = 0; i < payload.length; ++i) {
            buf[i] = payload[i];
        }
        if (payload.length > 0) {
            payload[0] = replacement;
        }
        if (payload.length > 1) {
            delete payload[1];
        }
        buf[payload.length] = bytes1(suffix);
        out = buf;
    }

    function echoOrEmpty(bytes memory payload, uint8 mode)
        public
        pure
        returns (bytes memory out)
    {
        if (mode == 0) {
            return out;
        }
        if (mode == 1) {
            return payload;
        }
        out = abi.encodePacked(payload, bytes1(mode));
    }

    function duplicateShared(uint8 seed, uint8 extraLen)
        external
        pure
        returns (bytes memory first, bytes memory second)
    {
        bytes memory shared = new bytes(uint256(extraLen) + 2);
        shared[0] = bytes1(seed);
        shared[1] = bytes1(seed ^ 0x5a);
        return (shared, shared);
    }

    function failOnBytes(bytes memory payload, uint8 kind)
        external
        pure
        returns (bytes memory)
    {
        if (kind == 0) {
            bytes1 head = payload.length > 0 ? payload[0] : bytes1(0);
            revert BadPayload(payload.length, head);
        }
        if (kind == 1) {
            require(payload.length > 1000, "short-payload");
            return payload;
        }
        bytes1 oob = payload[payload.length];
        return abi.encodePacked(oob);
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

    function addAmount(Counter storage c, uint256 amount) external {
        c.total += amount;
        c.calls += 1;
    }

    function sinkNarrow(Counter storage c, uint8, address, bytes4) external {
        c.calls += 1;
    }

    function sinkNarrowInternal(Counter storage c, uint8, address, bytes4) internal {
        c.calls += 1;
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

    function recordDigest(Counter storage c, bytes memory payload, bytes1 scrub)
        external
        returns (bytes memory, uint256)
    {
        bytes memory tagged = LinkedPackLib.mutateAndTag(payload, scrub, uint8(c.calls + 1));
        if (payload.length > 0) {
            payload[0] = bytes1(0xff);
        }
        c.total += uint256(keccak256(tagged)) & 0xffff;
        c.last = msg.sender;
        c.calls += 1;
        return (tagged, c.total);
    }
}

contract LinkedLibraryCallFixture {
    mapping(bytes32 => uint256) internal packedWords;
    mapping(bytes32 => LinkedCounterLib.Counter) internal counters;
    LinkedCounterLib.Counter internal main;
    uint256 internal lastWord;
    bytes internal storedPayload;

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

    function addExternal(bytes32 key, uint256 amount) external {
        LinkedCounterLib.addAmount(counters[key], amount);
    }

    function rawAddress(uint256 x) internal pure returns (address a) {
        assembly {
            a := x
        }
    }

    function cleanNarrow(
        uint256 rawU,
        uint256 rawS,
        uint256 rawFlag,
        uint256 rawWrapped,
        uint256 rawAddr,
        uint256 rawSel
    ) external pure returns (uint256 outU, uint256 outS, uint256 outFlag, uint256 outWrapped, uint256 outAddr, uint256 outSel) {
        {
            uint8 u = 0;
            assembly {
                u := rawU
            }
            uint8 singleU = LinkedPackLib.passUint8(u);
            assembly {
                outU := singleU
            }
        }
        {
            int8 s = 0;
            bool flag = false;
            Narrow8 wrapped = Narrow8.wrap(0);
            address addr = rawAddress(rawAddr);
            bytes4 sel = bytes4(0);
            assembly {
                s := rawS
                flag := rawFlag
                wrapped := rawWrapped
                sel := rawSel
            }
            (, int8 rS, bool rFlag, Narrow8 rWrapped, address rAddr, bytes4 rSel) =
                LinkedPackLib.roundTripNarrow(0, s, flag, wrapped, addr, sel);
            assembly {
                outS := rS
                outFlag := rFlag
                outWrapped := rWrapped
                outAddr := rAddr
                outSel := rSel
            }
        }
    }

    function cleanReturnFromWide(uint256 rawU, uint256 rawAddr, bytes32 rawSel)
        external
        pure
        returns (uint256, uint256, uint256)
    {
        uint8 rU = LinkedPackLib.narrowSingleFromWide(rawU);
        (address rAddr, bytes4 rSel) = LinkedPackLib.narrowMultiFromWide(rawAddr, rawSel);
        uint256 outU;
        uint256 outAddr;
        uint256 outSel;
        assembly {
            outU := rU
            outAddr := rAddr
            outSel := rSel
        }
        return (outU, outAddr, outSel);
    }

    function entryCleanVoid(bytes32 key, uint256 rawU, uint256 rawAddr, uint256 rawSel) external {
        uint8 u = 0;
        address addr = rawAddress(rawAddr);
        bytes4 sel = bytes4(0);
        assembly {
            u := rawU
            sel := rawSel
        }
        LinkedCounterLib.sinkNarrow(counters[key], u, addr, sel);
    }

    function internalRawVoid(bytes32 key, uint256 rawU, uint256 rawAddr, uint256 rawSel) external {
        uint8 u = 0;
        address addr = rawAddress(rawAddr);
        bytes4 sel = bytes4(0);
        assembly {
            u := rawU
            sel := rawSel
        }
        LinkedCounterLib.sinkNarrowInternal(counters[key], u, addr, sel);
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

    function _checkedDivSuffix(uint256 num, uint256 denom)
        internal
        pure
        returns (uint8)
    {
        return uint8(num / denom);
    }

    function roundTripBytesIsolation(
        bytes memory orig,
        bytes1 repl,
        bytes1 callerPost,
        uint8 suffix
    )
        external
        returns (
            uint8 orig0,
            uint8 orig1,
            uint8 ret0Before,
            uint8 ret0After,
            uint8 retLast,
            bytes32 retHash
        )
    {
        bytes memory ret = LinkedPackLib.mutateAndTag(orig, repl, suffix);
        orig0 = orig.length > 0 ? uint8(orig[0]) : 0;
        orig1 = orig.length > 1 ? uint8(orig[1]) : 0;
        ret0Before = uint8(ret[0]);
        ret[0] = callerPost;
        ret0After = uint8(ret[0]);
        retLast = uint8(ret[ret.length - 1]);
        retHash = keccak256(ret);
        lastWord = uint256(retHash);
    }

    function echoAndCallerMutate(bytes calldata raw, uint8 mode, bytes1 callerMut)
        external
        pure
        returns (bytes32 origHashAfter, bytes32 retHashAfter, uint256 retLen)
    {
        bytes memory local = new bytes(raw.length + 1);
        for (uint256 i = 0; i < raw.length; ++i) {
            local[i] = raw[i];
        }
        local[raw.length] = bytes1(uint8(0x44));
        bytes memory echoed = LinkedPackLib.echoOrEmpty(local, mode);
        local[0] = callerMut;
        if (echoed.length > 0) {
            echoed[echoed.length - 1] = bytes1(uint8(mode ^ 0x33));
        }
        return (keccak256(local), keccak256(echoed), echoed.length);
    }

    function duplicateDisjoint(uint8 seed, uint8 extraLen, bytes1 mutFirst)
        external
        pure
        returns (uint8 first0, uint8 second0, bytes32 firstHash, bytes32 secondHash)
    {
        (bytes memory first, bytes memory second) = LinkedPackLib.duplicateShared(seed, extraLen);
        first[0] = mutFirst;
        return (uint8(first[0]), uint8(second[0]), keccak256(first), keccak256(second));
    }

    function nestedBytesAndStorage(
        bytes32 key,
        bytes calldata sliceSrc,
        uint256 start,
        uint256 end,
        bytes1 scrub
    ) external returns (bytes32, uint256) {
        storedPayload = sliceSrc;
        (bytes memory nestedOut, uint256 running) =
            LinkedCounterLib.recordDigest(counters[key], sliceSrc[start:end], scrub);
        bytes memory fromStorage = LinkedPackLib.mutateAndTag(storedPayload, scrub, uint8(running));
        if (nestedOut.length > 0) {
            nestedOut[0] = bytes1(uint8(0xaa));
        }
        bytes32 combined = keccak256(nestedOut) ^ keccak256(fromStorage) ^ keccak256(storedPayload);
        lastWord = uint256(combined);
        return (combined, running);
    }

    function argOrderBytes(bytes memory orig, uint256 denom, bytes1 calleeRepl)
        external
        pure
        returns (uint8 origAfter, uint8 seenByCallee, uint8 suffixSeen)
    {
        bytes memory ret = LinkedPackLib.mutateAndTag(
            orig,
            calleeRepl,
            _checkedDivSuffix(90, denom)
        );
        origAfter = orig.length > 0 ? uint8(orig[0]) : 0;
        seenByCallee = uint8(ret[0]);
        suffixSeen = uint8(ret[ret.length - 1]);
    }

    function revertFromBytesLib(bytes32 key, bytes calldata payload, uint8 kind)
        external
        returns (uint256)
    {
        counters[key].calls += 1;
        bytes memory out = LinkedPackLib.failOnBytes(payload, kind);
        return out.length;
    }

    function mainState() external view returns (uint256, uint256) {
        return (main.total, lastWord);
    }
}
