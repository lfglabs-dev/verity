// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyRolesDeclaredSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Effects.lean
 */
contract PropertyRolesDeclaredSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYulWithArgs("RolesDeclaredSmoke", abi.encode(alice));
        require(target != address(0), "Deploy failed");
    }

    // Property 1: setByOwner enforces its required role
    function testAuto_SetByOwner_RejectsUnauthorizedCaller() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setByOwner(uint256)", uint256(1)));
        require(!ok, "setByOwner accepted an unauthorized caller");
    }
    // Property 2: setByAdmin enforces its required role
    function testAuto_SetByAdmin_RejectsUnauthorizedCaller() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("setByAdmin(uint256)", uint256(1)));
        require(!ok, "setByAdmin accepted an unauthorized caller");
    }
    // Property 3: mintLike enforces its required role
    function testAuto_MintLike_RejectsUnauthorizedCaller() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("mintLike(uint256)", uint256(1)));
        require(!ok, "mintLike accepted an unauthorized caller");
    }
    // Property 4: relayLike enforces its required role
    function testAuto_RelayLike_RejectsUnauthorizedCaller() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("relayLike(uint256)", uint256(1)));
        require(!ok, "relayLike accepted an unauthorized caller");
    }
}
