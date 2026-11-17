// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// solc reference: the same signatures, decoded by solc's ABI coder v2.
contract ScalarAbiValidationReference {
    function echoAddress(address value) external pure returns (address) { return value; }
    function echoBool(bool value) external pure returns (bool) { return value; }
    function echoBytes4(bytes4 value) external pure returns (bytes4) { return value; }
    function echoUint8(uint8 value) external pure returns (uint8) { return value; }
    function echoUint16(uint16 value) external pure returns (uint16) { return value; }
    function echoUint32(uint32 value) external pure returns (uint32) { return value; }
    function echoInt8(int8 value) external pure returns (int8) { return value; }
    function echoInt16(int16 value) external pure returns (int16) { return value; }
    function echoUint256(uint256 value) external pure returns (uint256) { return value; }
    function echoInt256(int256 value) external pure returns (int256) { return value; }
    function echoBytes32(bytes32 value) external pure returns (bytes32) { return value; }
    function firstOfMixed(uint256 full, uint8, address, bool) external pure returns (uint256) {
        return full;
    }
    struct Pair { uint256 first; address account; }
    function accountOfPair(Pair calldata pair) external pure returns (address) {
        return pair.account;
    }
}

/// Scalar head words of the compiled Verity contract are validated as by solc's ABI
/// coder v2: a word that is not a valid encoding of its narrow type reverts with empty
/// returndata, a clean word is echoed back unchanged.
contract ScalarAbiValidationSmokeTest is Test, YulTestBase {
    address internal smoke;
    address internal solcReference;

    string[11] internal echoes = [
        "echoAddress(address)", "echoBool(bool)", "echoBytes4(bytes4)", "echoUint8(uint8)",
        "echoUint16(uint16)", "echoUint32(uint32)", "echoInt8(int8)", "echoInt16(int16)",
        "echoUint256(uint256)", "echoInt256(int256)", "echoBytes32(bytes32)"
    ];

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.ScalarAbiValidationSmoke", "ScalarAbiValidationSmoke", _smokeYulDir());
        solcReference = address(new ScalarAbiValidationReference());
    }

    function _call(address target, string memory sig, bytes memory args)
        internal
        returns (bool ok, bytes memory data)
    {
        (ok, data) = target.call(abi.encodePacked(bytes4(keccak256(bytes(sig))), args));
    }

    function _assertEcho(string memory sig, uint256 word) internal {
        (bool ok, bytes memory data) = _call(smoke, sig, abi.encode(word));
        assertTrue(ok, string.concat(sig, ": clean word reverted"));
        assertEq(data, abi.encode(word), string.concat(sig, ": clean word not echoed"));
    }

    function _assertRejects(string memory sig, uint256 word) internal {
        (bool ok, bytes memory data) = _call(smoke, sig, abi.encode(word));
        assertFalse(ok, string.concat(sig, ": dirty word accepted"));
        assertEq(data.length, 0, string.concat(sig, ": revert data not empty"));
    }

    function _assertMatchesReference(string memory sig, bytes memory args) internal {
        (bool okRef, bytes memory dataRef) = _call(solcReference, sig, args);
        (bool ok, bytes memory data) = _call(smoke, sig, args);
        assertEq(ok, okRef, string.concat(sig, ": status differs from solc"));
        assertEq(data, dataRef, string.concat(sig, ": returndata differs from solc"));
    }

    function testAddressHighBitsReject() public {
        _assertEcho("echoAddress(address)", 0);
        _assertEcho("echoAddress(address)", type(uint160).max);
        _assertRejects("echoAddress(address)", uint256(1) << 160);
        _assertRejects("echoAddress(address)", (uint256(1) << 255) | 1);
        _assertRejects("echoAddress(address)", type(uint256).max);
    }

    function testBoolOtherThanZeroOrOneRejects() public {
        _assertEcho("echoBool(bool)", 0);
        _assertEcho("echoBool(bool)", 1);
        _assertRejects("echoBool(bool)", 2);
        _assertRejects("echoBool(bool)", 256);
        _assertRejects("echoBool(bool)", type(uint256).max);
    }

    function testBytes4LowBitsReject() public {
        _assertEcho("echoBytes4(bytes4)", 0);
        _assertEcho("echoBytes4(bytes4)", uint256(0xdeadbeef) << 224);
        _assertRejects("echoBytes4(bytes4)", 1);
        _assertRejects("echoBytes4(bytes4)", (uint256(0xdeadbeef) << 224) | (uint256(1) << 223));
        _assertRejects("echoBytes4(bytes4)", type(uint256).max);
    }

    function testUintNHighBitsReject() public {
        _assertEcho("echoUint8(uint8)", 255);
        _assertRejects("echoUint8(uint8)", 256);
        _assertEcho("echoUint16(uint16)", 65535);
        _assertRejects("echoUint16(uint16)", 65536);
        _assertEcho("echoUint32(uint32)", type(uint32).max);
        _assertRejects("echoUint32(uint32)", uint256(type(uint32).max) + 1);
        _assertRejects("echoUint32(uint32)", type(uint256).max);
    }

    function testIntNNotSignExtendedRejects() public {
        _assertEcho("echoInt8(int8)", 127);
        _assertEcho("echoInt8(int8)", uint256(int256(-128)));
        _assertEcho("echoInt8(int8)", type(uint256).max);
        _assertRejects("echoInt8(int8)", 128);
        _assertRejects("echoInt8(int8)", 255);
        _assertRejects("echoInt8(int8)", uint256(int256(-129)));
        _assertEcho("echoInt16(int16)", uint256(int256(type(int16).min)));
        _assertRejects("echoInt16(int16)", uint256(int256(type(int16).max)) + 1);
        _assertRejects("echoInt16(int16)", uint256(1) << 255);
    }

    function testFullWidthWordsAreNotValidated() public {
        _assertEcho("echoUint256(uint256)", type(uint256).max);
        _assertEcho("echoInt256(int256)", uint256(1) << 255);
        _assertEcho("echoBytes32(bytes32)", 1);
    }

    function testEveryHeadWordIsValidated() public {
        string memory sig = "firstOfMixed(uint256,uint8,address,bool)";
        uint256[4] memory base = [uint256(1) << 255, 127, (uint256(1) << 159) + 13, 1];
        (bool ok, bytes memory data) = _call(smoke, sig, abi.encode(base[0], base[1], base[2], base[3]));
        assertTrue(ok);
        assertEq(data, abi.encode(base[0]));
        uint256[4] memory dirty = [uint256(0), 256, uint256(1) << 160, 2];
        for (uint256 i = 1; i < 4; i++) {
            uint256[4] memory words = base;
            words[i] = dirty[i];
            (ok, data) = _call(smoke, sig, abi.encode(words[0], words[1], words[2], words[3]));
            assertFalse(ok, "dirty unread head word accepted");
            assertEq(data.length, 0);
        }
    }

    /// Biases a fuzzed word towards the clean encodings of each type, and their edges.
    function _shape(uint256 word, uint8 shape) internal pure returns (uint256) {
        if (shape % 6 == 1) return word & 1;
        if (shape % 6 == 2) return word & 0xffff;
        if (shape % 6 == 3) return word >> 96;
        if (shape % 6 == 4) return word << 224;
        if (shape % 6 == 5) return uint256(int256(int16(int256(word))));
        return word;
    }

    /// Known divergence, pinned so that a fix flips it: a dirty member of a static
    /// tuple parameter is masked by Verity, while solc reverts when it reads it.
    function testStaticTupleMemberIsMaskedNotValidated() public {
        string memory sig = "accountOfPair((uint256,address))";
        uint256 clean = (uint256(1) << 159) + 13;
        _assertMatchesReference(sig, abi.encode(uint256(7), clean));
        uint256 dirty = (uint256(1) << 160) | clean;
        (bool okRef, bytes memory dataRef) = _call(solcReference, sig, abi.encode(uint256(7), dirty));
        assertFalse(okRef, "solc accepted a dirty tuple member");
        assertEq(dataRef.length, 0);
        (bool ok, bytes memory data) = _call(smoke, sig, abi.encode(uint256(7), dirty));
        assertTrue(ok, "Verity now validates tuple members: update this test and the docs");
        assertEq(data, abi.encode(clean), "Verity no longer masks the tuple member");
    }

    function testFuzzMatchesSolcOnEveryScalarType(uint256 word, uint8 shape, uint8 which) public {
        _assertMatchesReference(echoes[which % echoes.length], abi.encode(_shape(word, shape)));
    }

    function testFuzzMatchesSolcOnMixedHead(uint256 a, uint256 b, uint256 c, uint256 d) public {
        _assertMatchesReference("firstOfMixed(uint256,uint8,address,bool)", abi.encode(a, b, c, d));
    }
}
