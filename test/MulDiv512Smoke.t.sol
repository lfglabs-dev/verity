// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Compiled `MulDiv512Smoke` against an exact 512-bit reference: the result must equal
/// floor/ceil(a * b / c) when it fits in uint256, and the call must revert otherwise.
contract MulDiv512SmokeTest is Test, YulTestBase {
    address internal yulContract;

    function setUp() public {
        yulContract = deployCompiledVerityModule(
            "Contracts.Smoke.MulDiv512Smoke",
            "MulDiv512Smoke",
            _smokeYulDir()
        );
    }

    /// Exact 512-bit product as (hi, lo).
    function _mul512(uint256 a, uint256 b) internal pure returns (uint256 hi, uint256 lo) {
        unchecked {
            uint256 mm = mulmod(a, b, type(uint256).max);
            lo = a * b;
            hi = mm - lo - (mm < lo ? 1 : 0);
        }
    }

    /// Reference floor/ceil quotient; `ok` is false when it does not fit (or c == 0).
    function _reference(uint256 a, uint256 b, uint256 c, bool up)
        internal
        pure
        returns (bool ok, uint256 q)
    {
        if (c == 0) return (false, 0);
        (uint256 hi, uint256 lo) = _mul512(a, b);
        if (hi >= c) return (false, 0);
        // hi < c: the quotient fits; long division by bits keeps the reference independent
        // of the helper's modular-inverse algorithm.
        uint256 rem = hi;
        for (uint256 i = 0; i < 256; i++) {
            bool carry = rem >> 255 == 1;
            rem = (rem << 1) | ((lo >> (255 - i)) & 1);
            q <<= 1;
            if (carry || rem >= c) {
                unchecked {
                    rem -= c;
                }
                q |= 1;
            }
        }
        if (up && rem != 0) {
            if (q == type(uint256).max) return (false, 0);
            q += 1;
        }
        return (true, q);
    }

    function _check(string memory sig, uint256 a, uint256 b, uint256 c, bool up) internal {
        (bool ok, uint256 want) = _reference(a, b, c, up);
        (bool success, bytes memory data) = yulContract.call(abi.encodeWithSignature(sig, a, b, c));
        assertEq(success, ok, "revert parity with exact reference");
        if (ok) {
            assertEq(abi.decode(data, (uint256)), want, "quotient");
        }
    }

    function testCeilRevertsWhenRoundedQuotientIs2Pow256() public {
        uint256 m = type(uint256).max;
        // floor((2^256-2)^2 / (2^256-3)) = 2^256-1 with a non-zero remainder.
        (bool success,) = yulContract.call(
            abi.encodeWithSignature("storeCeil(uint256,uint256,uint256)", m - 1, m - 1, m - 2)
        );
        assertFalse(success, "ceil of 2^256 must revert, not wrap to 0");
        _check("storeFloor(uint256,uint256,uint256)", m - 1, m - 1, m - 2, false);
    }

    function testEdgeCases() public {
        uint256 m = type(uint256).max;
        _check("storeCeil(uint256,uint256,uint256)", m, m, m, true);
        _check("storeFloor(uint256,uint256,uint256)", m, m, 1, false);
        _check("storeCeil(uint256,uint256,uint256)", 1, 1, 0, true);
        _check("storeCeil(uint256,uint256,uint256)", 3, 5, 2, true);
        _check("storeCeil(uint256,uint256,uint256)", m, 1 << 200, (1 << 201) + 3, true);
    }

    function testFuzzMatchesReference(uint256 a, uint256 b, uint256 c) public {
        _check("storeFloor(uint256,uint256,uint256)", a, b, c, false);
        _check("storeCeil(uint256,uint256,uint256)", a, b, c, true);
    }
}
