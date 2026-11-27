// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

interface IVenues {
    function counterparty(uint8 kind, bytes calldata p) external view returns (address);
    function tokens(uint8 kind, bytes calldata p) external view returns (address, address);
}

interface ISafe {
    function execTransactionFromModuleReturnData(address to, uint256 value, bytes calldata data, uint8 operation)
        external
        returns (bool success, bytes memory returnData);
    function notify(bytes calldata data) external;
}

/// A view callee whose answers are hashes of its exact calldata, so the caller's result
/// pins every byte the caller sent.
contract HashingVenues {
    fallback(bytes calldata) external returns (bytes memory) {
        bytes32 h = keccak256(msg.data);
        if (msg.sig == IVenues.counterparty.selector) {
            return abi.encode(address(uint160(uint256(h))));
        }
        return abi.encode(address(uint160(uint256(h))), address(uint160(uint256(h) >> 96)));
    }
}

/// Records the calldata of every call; answers with raw bytes, or reverts with raw bytes.
contract RecordingSafe {
    bytes public lastData;
    bytes internal answer;
    bool internal reverting;

    function setAnswer(bytes memory a, bool r) external {
        answer = a;
        reverting = r;
    }

    fallback(bytes calldata) external returns (bytes memory) {
        lastData = msg.data;
        bytes memory out = answer;
        if (reverting) {
            assembly {
                revert(add(out, 32), mload(out))
            }
        }
        return out;
    }
}

/// The same calls written in Solidity: the reference for which returndata solc rejects.
contract SolidityCaller {
    function forward(ISafe safe, address to, uint256 val, bytes calldata data, uint8 op)
        external
        returns (bool, uint256)
    {
        (bool ok, bytes memory ret) = safe.execTransactionFromModuleReturnData(to, val, data, op);
        return (ok, ret.length);
    }
}

/// Checks the ABI-frame typed-interface calls of InterfaceBytesCallSmoke against Solidity's
/// own encoding (`abi.encodeCall`, `abi.encodeWithSelector`) and decoding.
contract InterfaceBytesCallSmokeTest is Test, YulTestBase {
    address internal smoke;
    HashingVenues internal venues;
    RecordingSafe internal safe;
    SolidityCaller internal solidityRef;

    address internal constant TO = address(0xA11CE);
    address internal constant TOKEN = address(0x70CE1);

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.InterfaceBytesCallSmoke", "InterfaceBytesCallSmoke", _smokeYulDir()
        );
        venues = new HashingVenues();
        safe = new RecordingSafe();
        solidityRef = new SolidityCaller();
    }

    function _pattern(uint256 n, uint8 seed) internal pure returns (bytes memory b) {
        b = new bytes(n);
        for (uint256 i = 0; i < n; i++) {
            b[i] = bytes1(uint8(seed + i));
        }
    }

    function _lengths() internal pure returns (uint256[5] memory) {
        return [uint256(0), 1, 31, 32, 33];
    }

    function _word(bytes memory b, uint256 k) internal pure returns (uint256 w) {
        for (uint256 j = 0; j < 32; j++) {
            uint256 i = 32 * k + j;
            w = (w << 8) | (i < b.length ? uint256(uint8(b[i])) : 0);
        }
    }

    function _forward(bytes memory data) internal returns (bool, bytes memory) {
        return smoke.call(
            abi.encodeWithSignature(
                "forward(address,address,uint256,bytes,uint8)", address(safe), TO, uint256(7), data, uint8(3)
            )
        );
    }

    // ------------------------------------------------------------ calldata

    function testForwardedBytesCalldataMatchesSolidity() public {
        uint256[5] memory ns = _lengths();
        safe.setAnswer(abi.encode(true, bytes("")), false);
        for (uint256 i = 0; i < ns.length; i++) {
            bytes memory data = _pattern(ns[i], 0x11);
            (bool ok,) = _forward(data);
            assertTrue(ok, "forward reverted");
            assertEq(
                safe.lastData(),
                abi.encodeCall(ISafe.execTransactionFromModuleReturnData, (TO, 7, data, 3)),
                "forwarded calldata"
            );
        }
    }

    function testBuiltStaticPayloadMatchesSolidity() public {
        safe.setAnswer(abi.encode(true, bytes("")), false);
        (bool ok,) = smoke.call(
            abi.encodeWithSignature(
                "transferVia(address,address,address,uint256)", address(safe), TOKEN, TO, uint256(5)
            )
        );
        assertTrue(ok);
        bytes memory payload = abi.encodeWithSelector(bytes4(0xa9059cbb), TO, uint256(5));
        assertEq(
            safe.lastData(),
            abi.encodeCall(ISafe.execTransactionFromModuleReturnData, (TOKEN, 0, payload, 0)),
            "transfer payload"
        );
    }

    function testBuiltPayloadWithNestedBytesMatchesSolidity() public {
        uint256[5] memory ns = _lengths();
        safe.setAnswer(abi.encode(true, abi.encode(uint256(777))), false);
        for (uint256 i = 0; i < ns.length; i++) {
            bytes memory p = _pattern(ns[i], 0x41);
            (bool ok, bytes memory out) = smoke.call(
                abi.encodeWithSignature(
                    "venueSwapVia(address,address,uint8,bytes,uint256)",
                    address(safe),
                    address(venues),
                    uint8(2),
                    p,
                    uint256(9)
                )
            );
            assertTrue(ok, "venueSwapVia reverted");
            assertEq(abi.decode(out, (uint256)), 777, "bytesWord ret 0");
            bytes memory payload = abi.encodeWithSelector(bytes4(0x8c973081), uint8(2), p, uint256(9));
            assertEq(
                safe.lastData(),
                abi.encodeCall(ISafe.execTransactionFromModuleReturnData, (address(venues), 0, payload, 0)),
                "venue swap payload"
            );
        }
    }

    function testVoidMethodCalldataMatchesSolidity() public {
        uint256[5] memory ns = _lengths();
        safe.setAnswer("", false);
        for (uint256 i = 0; i < ns.length; i++) {
            bytes memory data = _pattern(ns[i], 0x21);
            (bool ok,) = smoke.call(abi.encodeWithSignature("notifyVia(address,bytes)", address(safe), data));
            assertTrue(ok, "notifyVia reverted");
            assertEq(safe.lastData(), abi.encodeCall(ISafe.notify, (data)), "notify calldata");
        }
    }

    function testViewCallsSendSolidityCalldata() public {
        uint256[5] memory ns = _lengths();
        for (uint256 i = 0; i < ns.length; i++) {
            bytes memory p = _pattern(ns[i], 0x61);
            bytes32 h = keccak256(abi.encodeCall(IVenues.counterparty, (4, p)));
            (bool ok, bytes memory out) = smoke.call(
                abi.encodeWithSignature("who(address,uint8,bytes)", address(venues), uint8(4), p)
            );
            assertTrue(ok, "who reverted");
            assertEq(abi.decode(out, (address)), address(uint160(uint256(h))), "counterparty calldata");

            h = keccak256(abi.encodeCall(IVenues.tokens, (4, p)));
            (ok, out) = smoke.call(
                abi.encodeWithSignature("tokensOf(address,uint8,bytes)", address(venues), uint8(4), p)
            );
            assertTrue(ok, "tokensOf reverted");
            (address a, address b) = abi.decode(out, (address, address));
            assertEq(a, address(uint160(uint256(h))), "tokens calldata (first)");
            assertEq(b, address(uint160(uint256(h) >> 96)), "tokens calldata (second)");
        }
    }

    // ------------------------------------------------------------ (bool, bytes) returns

    function _checkReturn(bool flag, bytes memory ret) internal {
        safe.setAnswer(abi.encode(flag, ret), false);
        (bool ok, bytes memory out) = _forward(hex"c0ffee");
        assertTrue(ok, "forward reverted");
        (bool f, uint256 len, uint256 w0, uint256 w1) = abi.decode(out, (bool, uint256, uint256, uint256));
        assertEq(f, flag, "ok flag");
        assertEq(len, ret.length, "bytesLength");
        assertEq(w0, _word(ret, 0), "bytesWord 0");
        assertEq(w1, _word(ret, 1), "bytesWord 1");
    }

    function testBoolBytesReturnsDecodeLikeSolidity() public {
        _checkReturn(true, "");
        _checkReturn(false, "");
        _checkReturn(true, _pattern(33, 0x81));
        _checkReturn(false, _pattern(33, 0x91));
        _checkReturn(true, _pattern(1, 0xa1));
        _checkReturn(true, _pattern(64, 0xb1));
    }

    /// Trailing returndata after the bytes does not leak into the padded last word.
    function testBytesWordIsZeroPadded() public {
        bytes memory ret = _pattern(33, 0x81);
        bytes memory answer = bytes.concat(abi.encode(true, ret), bytes32(type(uint256).max));
        // Overwrite the zero padding of the 33-byte value with junk.
        for (uint256 i = 64 + 32 + 33; i < 64 + 32 + 64; i++) {
            answer[i] = 0xff;
        }
        safe.setAnswer(answer, false);
        (bool ok, bytes memory out) = _forward("");
        assertTrue(ok);
        (, uint256 len,, uint256 w1) = abi.decode(out, (bool, uint256, uint256, uint256));
        assertEq(len, 33);
        assertEq(w1, _word(ret, 1), "bytesWord 1 masks junk after the data");
    }

    function testInnerCallFailureRevertsWithItsData() public {
        bytes memory reason = _pattern(33, 0xd1);
        safe.setAnswer(abi.encode(false, reason), false);
        (bool ok, bytes memory out) = smoke.call(
            abi.encodeWithSignature(
                "transferVia(address,address,address,uint256)", address(safe), TOKEN, TO, uint256(5)
            )
        );
        assertFalse(ok);
        assertEq(out, reason, "revertBytes data");
    }

    function testOuterRevertIsBubbledExactly() public {
        bytes memory reason = _pattern(37, 0xe1);
        safe.setAnswer(reason, true);
        (bool ok, bytes memory out) = _forward(hex"01");
        assertFalse(ok);
        assertEq(out, reason, "bubbled revert data");
    }

    // ------------------------------------------------------------ malformed returndata

    function _expectMalformed(bytes memory answer, string memory label) internal {
        safe.setAnswer(answer, false);
        (bool ok, bytes memory out) = _forward(hex"01");
        assertFalse(ok, label);
        assertEq(out.length, 0, label);
        // Solidity rejects the same returndata.
        (bool refOk,) = address(solidityRef).call(
            abi.encodeCall(SolidityCaller.forward, (ISafe(address(safe)), TO, 7, hex"01", 3))
        );
        assertFalse(refOk, string.concat(label, " (solc)"));
    }

    function testMalformedReturndataReverts() public {
        bytes memory good = abi.encode(true, _pattern(33, 0x81));
        // Short buffer: 63 bytes.
        bytes memory shortBuf = new bytes(63);
        _expectMalformed(shortBuf, "short head");
        // Bad offset: past the end.
        bytes memory badOffset = bytes.concat(good);
        badOffset[63] = 0xe0;
        _expectMalformed(badOffset, "offset past end");
        // Offset beyond 2^64.
        bytes memory hugeOffset = bytes.concat(good);
        hugeOffset[32] = 0x01;
        _expectMalformed(hugeOffset, "offset >= 2^64");
        // Overlong length.
        bytes memory longLen = bytes.concat(good);
        longLen[95] = 0x60;
        _expectMalformed(longLen, "length past end");
        // Length word missing: offset 64 with exactly 64 bytes.
        _expectMalformed(abi.encode(true, uint256(64)), "length word missing");
        // Non-boolean flag.
        bytes memory badFlag = bytes.concat(good);
        badFlag[31] = 0x02;
        _expectMalformed(badFlag, "flag not 0/1");
    }
}
