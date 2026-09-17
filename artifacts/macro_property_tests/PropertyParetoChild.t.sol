// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyParetoChildTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/MultiParent.lean
 */
contract PropertyParetoChildTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("ParetoChild", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: go has no unexpected revert
    function testAuto_Go_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("go()"));
        require(ok, "go reverted unexpectedly");
    }
    // Property 2: stop has no unexpected revert
    function testAuto_Stop_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("stop()"));
        require(ok, "stop reverted unexpectedly");
    }
}
