// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/// Solidity reference for the ABI of a function returning a static struct.
contract FeeConfigReference {
    struct FeeConfig {
        uint256 borrowTakerFeeRatio;
        uint256 lendMakerFeeRatio;
    }

    function goodReturn(uint256 borrowFee, uint256 lendFee) external pure returns (FeeConfig memory) {
        return FeeConfig(borrowFee, lendFee);
    }
}

/// `return FeeConfig.mk a b` from a function returning `FeeConfig` must return the
/// struct's ABI encoding, byte-identical to Solidity's.
contract NamedStructReturnSmokeTest is Test, YulTestBase {
    address internal smoke;
    FeeConfigReference internal ref;

    function setUp() public {
        smoke = deployCompiledVerityModule(
            "Contracts.Smoke.NamedStructReturnSmoke", "NamedStructReturnSmoke", _smokeYulDir()
        );
        ref = new FeeConfigReference();
    }

    function _bytesOf(address target, uint256 a, uint256 b) internal returns (bytes memory) {
        (bool ok, bytes memory data) =
            target.call(abi.encodeWithSignature("goodReturn(uint256,uint256)", a, b));
        assertTrue(ok, "goodReturn reverted");
        return data;
    }

    function testReturnsStructFields() public {
        FeeConfigReference.FeeConfig memory cfg =
            abi.decode(_bytesOf(smoke, 3, 4), (FeeConfigReference.FeeConfig));
        assertEq(cfg.borrowTakerFeeRatio, 3);
        assertEq(cfg.lendMakerFeeRatio, 4);
    }

    function testFuzzMatchesSolidityEncoding(uint256 a, uint256 b) public {
        assertEq(_bytesOf(smoke, a, b), _bytesOf(address(ref), a, b));
    }
}
