// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

/// Out-of-slice negative controls and pipeline-order checks for `bytes`-member memory structs.
contract BytesMemberStructOrderAndRejects {
    enum Kind {
        None,
        Exact,
        Prefix
    }

    struct Clause {
        uint8 parent;
        Kind kind;
        bytes payload;
    }

    struct WithString {
        uint256 tag;
        string label;
    }

    struct WithWords {
        Kind kind;
        bytes32[] words;
    }

    function namedReordered(bytes calldata data) external pure returns (uint256) {
        Clause memory c = Clause({payload: data[0:4], kind: Kind.Exact, parent: uint8(data.length - 4)});
        return uint256(c.parent) + c.payload.length;
    }

    function stringMemberConstruct() external pure returns (uint256) {
        WithString memory w = WithString(1, "abc");
        return w.tag;
    }

    function arrayMemberHelper() internal pure returns (WithWords memory) {
        return WithWords(Kind.None, new bytes32[](1));
    }

    function callArrayMemberHelper() external pure returns (uint256) {
        WithWords memory w = arrayMemberHelper();
        return uint256(w.kind);
    }

    function yulReadStruct(bytes calldata data) external pure returns (uint256 w) {
        Clause memory c = Clause(1, Kind.Exact, data);
        assembly {
            w := mload(c)
        }
    }

    function yulHashStruct(bytes calldata data) external pure returns (bytes32 h) {
        Clause memory c = Clause(1, Kind.Exact, data);
        assembly {
            h := keccak256(c, 96)
        }
    }

    function _walk(Clause memory c, uint256 depth) internal pure returns (uint256) {
        if (depth == 0) return c.payload.length;
        return _walk(c, depth - 1);
    }

    function recursiveWalk(bytes calldata data, uint256 depth) external pure returns (uint256) {
        Clause memory c = Clause(0, Kind.Exact, data);
        return _walk(c, depth);
    }
}

contract BytesMemberStructMixedRejects {
    struct MixedUnsupported {
        uint8 tag;
        bytes payload;
        bytes32[] items;
    }
    function mixedBytesAndArrayLocal() external pure returns (uint256) {
        MixedUnsupported memory m;
        return m.tag;
    }
}

contract BytesMemberStructConcatAndOrder {
    enum Kind {
        A,
        B,
        C
    }

    struct S {
        uint8 tag;
        Kind kind;
        bytes payload;
    }

    function caseConcatCond(bytes calldata data, bool flag) external pure returns (uint256, bytes32) {
        bytes memory b = data;
        if (flag) {
            b = bytes.concat(hex"abcdef");
        }
        S memory s = S(7, Kind.B, b);
        return (s.payload.length, keccak256(s.payload));
    }

    function caseConcatShare() external pure returns (bytes1, bytes1, bytes1) {
        unchecked {
            bytes memory b = new bytes(2);
            b = bytes.concat(hex"1122");
            S memory s1 = S(1, Kind.A, b);
            S memory s2 = S(2, Kind.B, b);
            b[0] = hex"aa";
            s1.payload[1] = hex"bb";
            return (s1.payload[0], s2.payload[1], b[1]);
        }
    }

    function _namedConcatHelper() internal pure returns (bytes memory out) {
        bytes memory pad = hex"1122334455";
        out = bytes.concat(hex"abcdef");
        pad;
    }

    function caseNamedHelperConcat() external pure returns (uint256, bytes32) {
        S memory s = S(9, Kind.C, _namedConcatHelper());
        return (s.payload.length, keccak256(s.payload));
    }

    function _multiConcatHelper() internal pure returns (S memory s, bytes memory out) {
        s = S(3, Kind.B, hex"99887766");
        out = bytes.concat(hex"cafebabe");
    }

    function caseMultiHelperConcat() external pure returns (uint256, bytes32) {
        (S memory s1, bytes memory b) = _multiConcatHelper();
        S memory s2 = S(s1.tag, s1.kind, b);
        return (s2.payload.length, keccak256(s2.payload));
    }

    function _panicRhs(bytes memory empty) internal pure returns (bytes1) {
        return empty[0];
    }

    function caseByteWriteOrder(uint256 zero) external pure returns (uint256) {
        S memory s = S(1, Kind.A, new bytes(2));
        bytes memory empty = hex"";
        s.payload[1 / zero] = _panicRhs(empty);
        return s.payload.length;
    }

    function _wipePayload(S memory p) internal pure returns (bytes1) {
        delete p.payload;
        return hex"77";
    }

    function caseByteWriteMutateBase() external pure returns (uint256) {
        S memory s = S(1, Kind.A, new bytes(2));
        s.payload[0] = _wipePayload(s);
        return s.payload.length;
    }

    function _mutateTag(S memory p) internal pure returns (uint8) {
        p.tag = 100;
        return 5;
    }

    function caseCompoundMutateBase() external pure returns (uint8) {
        S memory s = S(10, Kind.A, hex"11");
        s.tag += _mutateTag(s);
        return s.tag;
    }

    function caseMultiStructEncode() external pure returns (bytes32, uint256, uint256) {
        S memory emptyS;
        S memory fullS = S(77, Kind.C, new bytes(33));
        fullS.payload[32] = hex"fe";
        bytes memory enc = abi.encode(emptyS, uint256(99), fullS);
        bytes memory rawEmpty = abi.encode(emptyS);
        bytes memory rawFull = abi.encode(fullS);
        S memory decEmpty = abi.decode(rawEmpty, (S));
        S memory decFull = abi.decode(rawFull, (S));
        return (keccak256(enc), decEmpty.payload.length, uint256(uint8(decFull.payload[32])));
    }

    function _pickBytes(bool flag, bytes memory a) internal pure returns (bytes memory) {
        if (flag) return a;
        return hex"1122";
    }

    function caseGuardHelperShare(bool flag) external pure returns (bytes1, bytes1) {
        unchecked {
            bytes memory b = new bytes(2);
            b[0] = hex"41";
            b[1] = hex"42";
            S memory s = S(1, Kind.A, _pickBytes(flag, b));
            s.payload[0] = hex"ff";
            return (b[0], s.payload[0]);
        }
    }

    function caseStaticcallShare(address target) external view returns (bytes32, bytes32) {
        bytes memory p = hex"aabb";
        (bool ok, bytes memory ret) = target.staticcall(p);
        require(ok);
        S memory s = S(1, Kind.A, ret);
        if (s.payload.length > 0) {
            s.payload[0] = hex"ff";
        }
        return (keccak256(ret), keccak256(s.payload));
    }

    function _wipeIdx(S memory p) internal pure returns (uint256) {
        delete p.payload;
        return 0;
    }

    function caseByteWriteMutateIdx() external pure returns (bytes1, uint256) {
        unchecked {
            bytes memory b = new bytes(2);
            S memory s = S(1, Kind.A, b);
            s.payload[_wipeIdx(s)] = hex"77";
            return (b[0], s.payload.length);
        }
    }

    function _setTagRetStruct(S memory p) internal pure returns (S memory) {
        p.tag = 88;
        return S(5, Kind.B, hex"beef");
    }

    function _setTagRetUint(S memory p) internal pure returns (uint256) {
        p.tag = 88;
        return 99;
    }

    function caseAbiEncodeScalarBeforeMutatingStruct() external pure returns (bytes32, bytes32) {
        S memory p = S(10, Kind.A, hex"11");
        S memory q = S(10, Kind.A, hex"11");
        return (keccak256(abi.encode(p.tag, _setTagRetStruct(p))), keccak256(abi.encode(q.tag, _setTagRetUint(q))));
    }
}

contract BytesMemberStructUnheaderedRejects {
    enum Kind {
        A,
        B
    }

    struct S {
        uint8 tag;
        Kind kind;
        bytes payload;
    }

    function selfDelegateUnheadered(bytes calldata data) external returns (uint256) {
        (bool ok, bytes memory ret) = address(this).delegatecall(data);
        require(ok);
        S memory s = S(1, Kind.A, ret);
        return s.payload.length;
    }

    function selfDelegateAliasUnheadered(bytes calldata data) external returns (uint256) {
        (bool ok, bytes memory ret) = address(this).delegatecall(data);
        require(ok);
        bytes memory aliasBuf = ret;
        S memory s = S(1, Kind.A, aliasBuf);
        return s.payload.length;
    }

    function _idBytes(bytes memory x) internal pure returns (bytes memory) {
        return x;
    }

    function yulUnpaddedViaHelperStruct(address eoa) external view returns (bytes32 w) {
        bytes memory p = hex"aabb";
        (bool ok, bytes memory ret) = eoa.staticcall(p);
        require(ok);
        S memory s = S(1, Kind.A, _idBytes(ret));
        bytes memory b = s.payload;
        assembly {
            w := mload(add(b, 0x20))
        }
    }
}

contract BytesMemberStructForwardedAndKeccak {
    enum Kind {
        A,
        B
    }

    struct S {
        uint8 tag;
        Kind kind;
        bytes payload;
    }

    function _fwdHelper() internal pure returns (uint256 a, bytes memory out) {
        a = 77;
        out = abi.encode(uint256(123));
    }

    function _namedHex() internal pure returns (bytes memory out) {
        out = hex"11223344";
    }

    function _multiHex() internal pure returns (uint256 u, bytes memory out) {
        return (9, hex"11223344");
    }

    function fwdRootOut(bool flag) external pure returns (uint256 a, bytes memory out) {
        out = hex"11223344";
        S memory s = S(1, Kind.A, out);
        if (flag) return _fwdHelper();
        a = s.payload.length;
        out = s.payload;
    }

    function fwdLocalB(bool flag) external pure returns (uint256 a, bytes memory out) {
        bytes memory b;
        b = hex"11223344";
        S memory s = S(1, Kind.A, b);
        if (flag) return _fwdHelper();
        return (s.payload.length, s.payload);
    }

    function fwdNamedHelper(bool flag) external pure returns (uint256 a, bytes memory out) {
        S memory s = S(1, Kind.A, _namedHex());
        if (flag) return _fwdHelper();
        return (s.payload.length, s.payload);
    }

    function fwdMultiHelper(bool flag) external pure returns (uint256 a, bytes memory out) {
        (uint256 u, bytes memory b) = _multiHex();
        S memory s = S(uint8(u), Kind.A, b);
        if (flag) return _fwdHelper();
        return (s.payload.length, s.payload);
    }

    function _mutatePayloadRetStruct(S memory p) internal pure returns (S memory) {
        p.payload[0] = hex"ff";
        return S(5, Kind.B, hex"beef");
    }

    function _mutatePayloadRetUint(S memory p) internal pure returns (uint256) {
        p.payload[0] = hex"ff";
        return 99;
    }

    function encodeKeccakBeforeMutate() external pure returns (bytes32, bytes32) {
        unchecked {
            bytes memory b1 = new bytes(2);
            b1[0] = hex"11";
            S memory p = S(10, Kind.A, b1);
            bytes memory b2 = new bytes(2);
            b2[0] = hex"11";
            S memory q = S(10, Kind.A, b2);
            return (
                keccak256(abi.encode(keccak256(b1), _mutatePayloadRetStruct(p))),
                keccak256(abi.encode(keccak256(b2), _mutatePayloadRetUint(q)))
            );
        }
    }

    function _storeA(S memory p, bytes memory b) internal pure {
        p.payload = b;
    }

    function _storeB(S memory p, bytes memory b) internal pure {
        p.payload = b;
        p.tag = 2;
    }

    function caseBranchFnPtrShare(bool flag) external pure returns (bytes1, bytes1) {
        unchecked {
            bytes memory b = new bytes(2);
            S memory p = S(1, Kind.A, hex"");
            function(S memory, bytes memory) internal pure fp = flag ? _storeA : _storeB;
            fp(p, b);
            p.payload[0] = hex"ff";
            return (b[0], p.payload[0]);
        }
    }
}

contract BytesMemberStructR5Rejects {
    enum Kind {
        A,
        B
    }

    struct S {
        uint8 tag;
        Kind kind;
        bytes payload;
    }

    function stringCastDirect(string memory str) external pure returns (uint256) {
        S memory s = S(1, Kind.A, bytes(str));
        return s.payload.length;
    }

    function stringCastViaLocal(string memory str) external pure returns (uint256) {
        bytes memory b = bytes(str);
        S memory s = S(1, Kind.A, b);
        return s.payload.length;
    }

    function emptyBytesYulWordLoad(bool flag) external pure returns (bytes32 w, uint256 t) {
        S memory emptyS;
        emptyS.tag = 77;
        bytes memory b;
        if (flag) {
            b = hex"11";
        }
        assembly {
            w := mload(add(b, 0x20))
        }
        t = emptyS.tag;
    }

    function asmInBytesStructClosure(uint256 x) external pure returns (uint256 w) {
        S memory emptyS;
        emptyS.tag = 77;
        assembly { w := x }
    }

    function namedStringRetCast() external pure returns (string memory out) {
        out = "hello";
        bytes memory b = bytes(out);
        S memory s = S(1, Kind.A, b);
        if (s.payload.length == 0) out = "";
    }

    function condStringCast(bool flag, string memory str) external pure returns (uint256) {
        bytes memory b = bytes(flag ? str : str);
        S memory s = S(1, Kind.A, b);
        return s.payload.length;
    }

    function selfDelegateCondUnheadered(bytes calldata data, bool flag) external returns (uint256) {
        (bool ok, bytes memory ret) = address(this).delegatecall(data);
        require(ok);
        bytes memory aliasBuf = flag ? ret : ret;
        S memory s = S(1, Kind.A, aliasBuf);
        return s.payload.length;
    }

    function _consumeMemS(S memory p) internal pure returns (uint256) {
        return p.payload.length;
    }

    function calldataToMemScratchAsm(S calldata c, uint256 x) external pure returns (uint256) {
        uint256 sum = _consumeMemS(c) + x;
        assembly { mstore(0, sum) return(0, 32) }
    }
}

contract BytesMemberStructR7Cases {
    struct S2 {
        uint256 a;
        uint256 b;
        bytes payload;
    }

    struct Inner {
        uint8 a;
        bytes b;
    }

    struct Outer {
        uint8 tag;
        Inner sub;
    }

    function casePosCtorAssign() external pure returns (uint256, uint256) {
        uint256 x = 10;
        S2 memory s = S2(x, (x = 99), hex"11");
        return (s.a, s.b);
    }

    function casePosCtorPostInc() external pure returns (uint256, uint256) {
        uint256 x = 10;
        S2 memory s = S2(x, x++, hex"11");
        return (s.a, s.b);
    }

    function stringCastReassignByteWrite() external pure returns (bytes1) {
        unchecked {
            string memory str = "ab";
            bytes memory b = new bytes(2);
            b = bytes(str);
            b[0] = hex"ff";
            return bytes(str)[0];
        }
    }

    function deleteNewBytesYul() external pure returns (uint256 isZeroSlot) {
        unchecked {
            bytes memory v = new bytes(2);
            delete v;
            assembly { isZeroSlot := eq(v, 0x60) }
        }
    }

    function concatReassignBytesYulWrite() external pure returns (bytes1) {
        unchecked {
            bytes memory v = new bytes(2);
            v = bytes.concat(hex"1122");
            assembly { mstore8(add(v, 0x20), 0xff) }
            return v[0];
        }
    }

    function nestedOuterBytesWriteAsm(Outer memory o) external pure returns (uint8) {
        o.sub.b = hex"1122";
        assembly { mstore8(0x140, 0xff) }
        return uint8(o.sub.b[0]);
    }
}

contract BytesMemberStructR8Cases {
    struct Inner {
        uint8 a;
        bytes b;
    }

    struct Outer {
        uint8 tag;
        Inner sub;
    }

    function caseYulOverwriteViaBytesCast(address target) external view returns (bytes32) {
        string memory str = "0123";
        bytes memory b = bytes(str);
        uint256 ok;
        assembly { ok := staticcall(gas(), target, 0, 0, add(b, 0x20), mload(b)) }
        require(ok == 1);
        return keccak256(bytes(str));
    }

    function caseYulOverwriteViaStringReadBytes(address target) external view returns (bytes32) {
        string memory str = "0123";
        bytes memory b = bytes(str);
        uint256 ok;
        assembly { ok := staticcall(gas(), target, 0, 0, add(str, 0x20), mload(str)) }
        require(ok == 1);
        return keccak256(b);
    }

    function caseNewStringCastYulMstore() external pure returns (bytes1, bytes1) {
        unchecked {
            string memory str = new string(2);
            bytes memory b = bytes(str);
            assembly { mstore8(add(str, 0x20), 0xff) }
            return (bytes(str)[0], b[0]);
        }
    }

    function nestedCalldataToMemCorruptAsm(Outer calldata o) external pure returns (bytes32) {
        bytes memory pad = hex"aa";
        Outer memory m = o;
        if (pad.length == 999) return bytes32(0);
        assembly { mstore8(0x180, 0xff) }
        return keccak256(abi.encode(m));
    }

    function stringRoundtripRawByteWrite(bool flag) external pure returns (bytes1) {
        unchecked {
            bytes memory raw = new bytes(2);
            string memory str = flag ? string(raw) : "ab";
            bytes memory b = bytes(str);
            raw[0] = hex"ff";
            return b[0];
        }
    }

    struct S {
        uint256 tag;
        bytes payload;
    }

    function _toStrTuple(bytes memory p) internal pure returns (string memory, uint256) {
        return (string(p), 1);
    }

    function multiStringStructMutate(bytes calldata init) external pure returns (uint256) {
        S memory m = S(1, init);
        (string memory str, uint256 u) = _toStrTuple(m.payload);
        bytes memory b = bytes(str);
        m.payload[0] = hex"ff";
        return (uint256(uint8(b[0])) << 8) | (u == 1 ? uint256(uint8(m.payload[0])) : 0);
    }

    function namedStringRetStructMutate(bytes calldata init, bool checkB) external pure returns (string memory out) {
        S memory m = S(1, init);
        out = string(m.payload);
        bytes memory b = bytes(out);
        m.payload[0] = hex"ff";
        if (checkB && b[0] == hex"ff") {
            out = "hit";
        }
    }

    function namedDynTupleStringStructMutate(bytes calldata init) external pure returns (uint256 code, string memory out) {
        S memory m = S(1, init);
        out = string(m.payload);
        bytes memory b = bytes(out);
        m.payload[0] = hex"ff";
        code = (uint256(uint8(b[0])) << 8) | uint256(uint8(m.payload[0]));
    }

    function newBytesStructHopRawMutate() external pure returns (uint256) {
        unchecked {
            bytes memory raw = new bytes(2);
            S memory m = S(1, raw);
            (string memory str, uint256 u) = _toStrTuple(m.payload);
            bytes memory b = bytes(str);
            raw[0] = hex"ff";
            return (uint256(uint8(b[0])) << 8) | (u == 1 ? uint256(uint8(m.payload[0])) : 0);
        }
    }
}
