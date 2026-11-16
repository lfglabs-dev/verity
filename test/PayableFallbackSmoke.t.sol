// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// `fallback payable` compiles to a fallback without the callvalue guard, like Solidity's
/// `fallback() external payable`; a plain `fallback` keeps the guard.
///
/// Contracts under test (Contracts/Smoke/Declarations.lean):
///   PayableFallbackSmoke:   fallback payable stores msgValue in slot 0, no receive.
///   SpecialEntrypointSmoke: plain fallback counts calls in fallbackCount, has a receive.
contract PayableFallbackSmokeTest is Test, YulTestBase {
    address internal payableFallback;
    address internal plainFallback;

    // A selector matching no function of either contract, followed by extra bytes.
    bytes internal constant UNKNOWN_CALLDATA = hex"deadbeef0000000000000000000000000000000000000000000000000000000000002a";

    function setUp() public {
        payableFallback = deployCompiledVerityModule(
            "Contracts.Smoke.PayableFallbackSmoke", "PayableFallbackSmoke", _smokeYulDir());
        plainFallback = deployCompiledVerityModule(
            "Contracts.Smoke.SpecialEntrypointSmoke", "SpecialEntrypointSmoke", _smokeYulDir());
    }

    function _uintView(address target, string memory sig) internal view returns (uint256) {
        (bool ok, bytes memory out) = target.staticcall(abi.encodeWithSignature(sig));
        require(ok, string.concat(sig, " reverted"));
        return abi.decode(out, (uint256));
    }

    function _payableFallbackCall(uint256 value, bytes memory data) internal {
        value = bound(value, 0, 1_000_000 ether);
        vm.deal(address(this), value);
        uint256 balanceBefore = payableFallback.balance;
        (bool ok,) = payableFallback.call{value: value}(data);
        assertTrue(ok, "payable fallback reverted");
        assertEq(_uintView(payableFallback, "getFallbackValue()"), value, "fallback did not record msg.value");
        assertEq(payableFallback.balance - balanceBefore, value, "value not kept");
    }

    function testFuzzPayableFallbackUnknownSelector(uint256 value) public {
        _payableFallbackCall(value, UNKNOWN_CALLDATA);
    }

    // No receive: empty calldata also reaches the fallback.
    function testFuzzPayableFallbackEmptyCalldata(uint256 value) public {
        _payableFallbackCall(value, "");
    }

    function testPayableFallbackZeroValue() public {
        _payableFallbackCall(0, UNKNOWN_CALLDATA);
        _payableFallbackCall(0, "");
    }

    function testPayableFallbackPositiveValue() public {
        _payableFallbackCall(1 ether, UNKNOWN_CALLDATA);
        _payableFallbackCall(7, "");
    }

    function testFuzzPlainFallbackRejectsValue(uint256 value) public {
        value = bound(value, 1, 1_000_000 ether);
        vm.deal(address(this), value);
        (bool ok,) = plainFallback.call{value: value}(UNKNOWN_CALLDATA);
        assertFalse(ok, "plain fallback accepted value");
        assertEq(_uintView(plainFallback, "getFallbackCount()"), 0);
        assertEq(plainFallback.balance, 0);
    }

    function testPlainFallbackAcceptsZeroValue() public {
        (bool ok,) = plainFallback.call(UNKNOWN_CALLDATA);
        assertTrue(ok, "plain fallback reverted on zero value");
        assertEq(_uintView(plainFallback, "getFallbackCount()"), 1);
        (ok,) = plainFallback.call{value: 0}(UNKNOWN_CALLDATA);
        assertTrue(ok);
        assertEq(_uintView(plainFallback, "getFallbackCount()"), 2);
    }
}
