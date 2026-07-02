// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

/**
 * @title Issue2074ImmutableDeployTest
 * @notice Regression test for lfglabs-dev/verity#2074.
 * @dev Deploys a contract that has an `immutables` block via REAL creation
 *      bytecode (EVM CREATE), then reads `loadimmutable`-backed views. Before
 *      the fix, the constructor emitted `setimmutable` before `datacopy` (and
 *      at the code offset `dataoffset("runtime")` instead of memory offset 0),
 *      so the runtime image returned by `return(0, …)` was never patched and
 *      every `loadimmutable` in the deployed code read `0`.
 *
 *      Contract under test: `ImmutableSmoke` (Contracts/Smoke/Declarations.lean)
 *        immutables
 *          seededSupply : Uint256 := (add seed offset)   -- offset = 2
 *          treasury     : Address := ownerSeed
 *        constructor (seed, ownerSeed) := setStorageAddr owner ownerSeed
 *        view supplyCap()    := seededSupply
 *        view treasuryAddr() := treasury
 */
contract Issue2074ImmutableDeployTest is Test, YulTestBase {
    /// Deploy `ImmutableSmoke` from freshly compiled Yul, appending ABI-encoded
    /// constructor args to the creation bytecode (real CREATE).
    function _deployImmutableSmoke(bytes memory args) internal returns (address) {
        _ensureVerityModuleYul("Contracts.Smoke.ImmutableSmoke", "ImmutableSmoke", _smokeYulDir());
        string memory path = string.concat(_smokeYulDir(), "/ImmutableSmoke.yul");
        bytes memory initCode = bytes.concat(_compileYul(path), args);
        return _deploy(initCode);
    }

    // A plain immutable (treasury := ownerSeed) is read back verbatim.
    function testImmutableAddressReadBack() public {
        address ownerSeed = address(0xBEEF);
        address target = _deployImmutableSmoke(abi.encode(uint256(1), ownerSeed));
        require(target != address(0), "Deploy failed");

        (bool ok, bytes memory ret) = target.staticcall(abi.encodeWithSignature("treasuryAddr()"));
        require(ok, "treasuryAddr reverted");
        assertEq(ret.length, 32, "treasuryAddr return length");
        assertEq(abi.decode(ret, (address)), ownerSeed, "immutable address must survive deploy (not 0)");
    }

    // A computed immutable (seededSupply := seed + offset) is read back.
    function testImmutableComputedReadBack() public {
        uint256 seed = 40;
        address target = _deployImmutableSmoke(abi.encode(seed, address(0xBEEF)));
        require(target != address(0), "Deploy failed");

        (bool ok, bytes memory ret) = target.staticcall(abi.encodeWithSignature("supplyCap()"));
        require(ok, "supplyCap reverted");
        assertEq(ret.length, 32, "supplyCap return length");
        // offset constant is 2, so seededSupply == seed + 2.
        assertEq(abi.decode(ret, (uint256)), seed + 2, "computed immutable must survive deploy (not 0)");
    }

    // Fuzzed: whatever constructor args are supplied, the deployed views echo them.
    function testImmutablesFuzz(uint128 seed, address ownerSeed) public {
        address target = _deployImmutableSmoke(abi.encode(uint256(seed), ownerSeed));
        require(target != address(0), "Deploy failed");

        (bool ok1, bytes memory r1) = target.staticcall(abi.encodeWithSignature("supplyCap()"));
        require(ok1, "supplyCap reverted");
        assertEq(abi.decode(r1, (uint256)), uint256(seed) + 2, "supplyCap == seed + offset");

        (bool ok2, bytes memory r2) = target.staticcall(abi.encodeWithSignature("treasuryAddr()"));
        require(ok2, "treasuryAddr reverted");
        assertEq(abi.decode(r2, (address)), ownerSeed, "treasuryAddr == ownerSeed");
    }
}
