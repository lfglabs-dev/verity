// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

struct Quote {
    uint256 amount;
    address payer;
}

/// Returns fixed multi-word values; `dirty` puts garbage in the address word's high bits.
contract CompositePool {
    bool public dirty;

    function setDirty(bool d) external {
        dirty = d;
    }

    function fetchPair() external view returns (uint256, address) {
        if (dirty) {
            assembly {
                mstore(0, 11)
                mstore(32, or(shl(160, 1), 0xBEEF))
                return(0, 64)
            }
        }
        return (11, address(0xBEEF));
    }

    function fetchNested() external pure returns (uint256[2] memory, uint256) {
        return ([uint256(21), 22], 23);
    }

    function fetchQuote() external pure returns (Quote memory) {
        return Quote(31, address(0xCAFE));
    }
}

/// `let result ← pool.f; return result` for a composite return must forward every word,
/// not only the first one.
contract InterfaceCompositeReturnSmokeTest is Test, YulTestBase {
    address internal smoke;
    CompositePool internal pool;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.InterfaceCompositeReturnSmoke", "InterfaceCompositeReturnSmoke", _smokeYulDir()
        );
        pool = new CompositePool();
    }

    function _call(string memory sig) internal returns (bool, bytes memory) {
        return smoke.call(abi.encodeWithSignature(sig, address(pool)));
    }

    function testTupleReturnForwardsBothWords() public {
        (bool ok, bytes memory data) = _call("pair(address)");
        assertTrue(ok);
        (uint256 amount, address who) = abi.decode(data, (uint256, address));
        assertEq(amount, 11);
        assertEq(who, address(0xBEEF));
    }

    function testNestedFixedArrayReturnForwardsAllWords() public {
        (bool ok, bytes memory data) = _call("nested(address)");
        assertTrue(ok);
        (uint256[2] memory xs, uint256 last) = abi.decode(data, (uint256[2], uint256));
        assertEq(xs[0], 21);
        assertEq(xs[1], 22);
        assertEq(last, 23);
    }

    function testStructReturnForwardsAllFields() public {
        (bool ok, bytes memory data) = _call("quote(address)");
        assertTrue(ok);
        Quote memory q = abi.decode(data, (Quote));
        assertEq(q.amount, 31);
        assertEq(q.payer, address(0xCAFE));
    }

    /// Like every single-word external result in Verity, an address leaf is masked to
    /// 160 bits (Solidity's decoder would revert instead).
    function testDirtyAddressWordIsMasked() public {
        pool.setDirty(true);
        (bool ok, bytes memory data) = _call("pair(address)");
        assertTrue(ok);
        (uint256 amount, address who) = abi.decode(data, (uint256, address));
        assertEq(amount, 11);
        assertEq(who, address(0xBEEF));
    }
}
