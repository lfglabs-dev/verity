// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Solidity reference for the same functions.
contract WholeCompositeReference {
    struct Quote {
        uint256 amount;
        uint256 fee;
    }

    function echoFixed(uint256[3] calldata arr) external pure returns (uint256[3] memory) {
        return arr;
    }

    function viaHelper(uint256[2] calldata arr) external pure returns (uint256[2] memory) {
        return arr;
    }

    function quoteOf(uint256 a) external pure returns (Quote memory) {
        return Quote(a, a + 1);
    }

    function echoQuote(Quote calldata q) external pure returns (Quote memory) {
        return q;
    }
}

/// Every whole fixed-array / struct value must keep all its words: the return
/// data is byte-identical to Solidity's.
contract WholeCompositeValueSmokeTest is Test, YulTestBase {
    address internal smoke;
    address internal ref;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.WholeCompositeValueSmoke", "WholeCompositeValueSmoke", _smokeYulDir()
        );
        ref = address(new WholeCompositeReference());
    }

    function _same(bytes memory callData) internal {
        (bool okV, bytes memory outV) = smoke.call(callData);
        (bool okS, bytes memory outS) = ref.call(callData);
        assertTrue(okV, "verity call reverted");
        assertTrue(okS, "reference call reverted");
        assertEq(outV, outS);
    }

    function testFuzzEchoFixed(uint256 a, uint256 b, uint256 c) public {
        _same(abi.encodeWithSignature("echoFixed(uint256[3])", [a, b, c]));
    }

    function testFuzzFixedThroughHelper(uint256 a, uint256 b) public {
        _same(abi.encodeWithSignature("viaHelper(uint256[2])", [a, b]));
    }

    function testFuzzStructFromHelper(uint128 a) public {
        _same(abi.encodeWithSignature("quoteOf(uint256)", uint256(a)));
    }

    function testFuzzEchoStruct(uint256 a, uint256 b) public {
        _same(abi.encodeWithSignature("echoQuote((uint256,uint256))", a, b));
    }
}
