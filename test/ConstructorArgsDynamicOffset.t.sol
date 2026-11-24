// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/**
 * @title ConstructorArgsDynamicOffsetTest
 * @notice The head offset of a dynamic constructor argument is bounds checked
 *         before it is rebased onto the copied arguments.
 * @dev The arguments are copied to memory offset 128 and a `string` head word
 *      resolves to `add(128, offset)`. Checking only that rebased value against
 *      the end of the arguments let an offset of `2^256 - 128 + k` wrap to `k`
 *      and read its length word from scratch space; solc rejects such an
 *      offset. The loader now bounds the head word itself.
 *
 *      Contract under test: `ConstructorStringArgSmoke`
 *      (Contracts/Smoke/ConstructorStringArgSmoke.lean):
 *      `constructor(string _name, uint256 initialSupply)` stores the supply.
 */
contract ConstructorArgsDynamicOffsetTest is Test, YulTestBase {
    uint256 internal constant SUPPLY = 1000;

    function _initCode() internal returns (bytes memory) {
        _ensureVerityModuleYul(
            "Contracts.Smoke.ConstructorStringArgSmoke", "ConstructorStringArgSmoke", _smokeYulDir()
        );
        return _compileYul(string.concat(_smokeYulDir(), "/ConstructorStringArgSmoke.yul"));
    }

    /// Deploy with `args` appended to the initcode; zero when the deployment reverts.
    function _tryDeploy(bytes memory args) internal returns (address target) {
        bytes memory initCode = bytes.concat(_initCode(), args);
        assembly {
            target := create(0, add(initCode, 0x20), mload(initCode))
        }
    }

    function _assertDeployed(bytes memory args) internal {
        address target = _tryDeploy(args);
        require(target != address(0), "deployment reverted");
        (bool ok, bytes memory ret) = target.staticcall(abi.encodeWithSignature("get()"));
        require(ok, "get reverted");
        assertEq(abi.decode(ret, (uint256)), SUPPLY, "stored supply");
    }

    function testValidEncoding() public {
        _assertDeployed(abi.encode("verity", SUPPLY));
    }

    function testEmptyString() public {
        _assertDeployed(abi.encode("", SUPPLY));
    }

    /// `2^256 - 128` rebases to 0: the length word would be read from scratch space.
    function testOffsetWrappingToScratchReverts() public {
        assertEq(_tryDeploy(abi.encode(type(uint256).max - 127, SUPPLY)), address(0));
    }

    /// `2^256 - 96` rebases to 32, still below the copied arguments.
    function testOffsetWrappingBelowArgsReverts() public {
        assertEq(_tryDeploy(abi.encode(type(uint256).max - 95, SUPPLY)), address(0));
    }

    function testOffsetPastArgsReverts() public {
        assertEq(_tryDeploy(abi.encode(uint256(96), SUPPLY)), address(0));
    }

    function testOffsetInsideHeadReverts() public {
        assertEq(_tryDeploy(abi.encode(uint256(0), SUPPLY)), address(0));
    }

    /// The string's padded data word is missing: length exceeds the remaining tail.
    function testTruncatedStringReverts() public {
        bytes memory args = abi.encode("verity", SUPPLY);
        bytes memory truncated = new bytes(args.length - 32);
        for (uint256 i = 0; i < truncated.length; i++) truncated[i] = args[i];
        assertEq(_tryDeploy(truncated), address(0));
    }
}
